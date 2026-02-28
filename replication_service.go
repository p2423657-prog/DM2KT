package main

import (
	"bufio"
	"crypto/sha256"
	"encoding/json"
	"fmt"
	"io/ioutil"
	"math"
	"math/big"
	"math/rand/v2"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"sync"
	"sync/atomic" // 用于流量拥堵测试的计数器
	"time"
)

// --- 1. 配置与常量 ---

const (
	N_REGIONS             = 3
	KEYSPACE_TRITS_ALL    = 3 //构建ALLtree时取后三位展示分布
	KEYSPACE_TRITS_REGION = 2 //regiontree上节点后两位展示分布
	OFFSET                = 1
	ID_TRIT_WIDTH         = 27
	ROOT_STORAGE_DIR      = "./network_storage"  // 模拟节点的磁盘根目录
	DOWNLOAD_DIR          = "./client_downloads" // 客户端下载目录
	NODE_BANDWIDTH        = 50 * 1024 * 1024     // 模拟节点带宽: 50MB/s (即 400Mbps)
	TEST_FILE_SIZE        = 100 * 1024 * 1024    // 模拟文件大小: 100MB
)

type ID uint64

// StorageLocation 记录文件内容的物理位置 (路标)
type StorageLocation struct {
	PrimaryNodeID     ID
	BackupNodeID      ID
	CrossNodeID       ID
	OriginalPrimaryID ID
}

type FileMetadata struct {
	Name      string          `json:"name"`
	Type      string          `json:"type"`
	Owner     string          `json:"owner"`
	Size      int64           `json:"size"`
	FileID    ID              `json:"file_id"`   // 原始文件的 ID
	Locations StorageLocation `json:"locations"` // 指向物理数据的指针
}

type Node struct {
	Name           string
	ID             ID
	RegionIndex    int
	StoragePath    string
	ActiveRequests int64
	Bandwidth      float64
	RAM            int64
}

type Region struct {
	Index          int
	Nodes          []*Node
	RegionCenterID ID
	Representative *Node
	BackupRegionID int
}

type Cluster struct {
	NodeIndices []int
	Index       int
}

// 传输统计数据
type TransferStats struct {
	TotalPackets    int
	LostPackets     int
	Retransmissions int
	ActualBandwidth float64
	TotalDuration   time.Duration
}

var DeadNodeMap = make(map[ID]bool)

func isNodeAlive(id ID) bool {
	return !DeadNodeMap[id]
}

func loadRTTData(filename string) ([]string, [][]float64) {
	file, err := os.ReadFile(filename)
	if err != nil {
		// 为了方便直接运行，如果没有数据文件，这里生成一个简单的伪造数据
		fmt.Printf("警告: 无法读取 %s (%v)，将使用随机模拟数据。\n", filename, err)
		return generateMockRTT(15)
	}

	var rttMap map[string]map[string]float64
	if err := json.Unmarshal(file, &rttMap); err != nil {
		panic(fmt.Sprintf("解析 RTT JSON 失败: %v", err))
	}

	nodeNames := make([]string, 0, len(rttMap))
	for name := range rttMap {
		nodeNames = append(nodeNames, name)
	}
	sort.Strings(nodeNames)

	n := len(rttMap)
	matrix := make([][]float64, n)
	for i := 0; i < n; i++ {
		matrix[i] = make([]float64, n)
		for j := 0; j < n; j++ {
			if i == j {
				matrix[i][j] = 0
			} else {
				if val, ok := rttMap[nodeNames[i]][nodeNames[j]]; ok {
					matrix[i][j] = val
				} else {
					matrix[i][j] = math.MaxFloat64
				}
			}
		}
	}
	return nodeNames, matrix
}

// 辅助函数：生成模拟 RTT 数据（防止用户没有 JSON 文件导致无法运行）
func generateMockRTT(n int) ([]string, [][]float64) {
	names := make([]string, n)
	matrix := make([][]float64, n)
	for i := 0; i < n; i++ {
		names[i] = fmt.Sprintf("Node_%02d", i+1)
		matrix[i] = make([]float64, n)
	}
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			if i == j {
				matrix[i][j] = 0
			} else {
				dist := math.Abs(float64(i - j))
				matrix[i][j] = dist * 10 // 10ms per index distance
			}
		}
	}
	return names, matrix
}

// --- 2. 基础算法逻辑 (保持三进制逻辑) ---
func hashFunc(data string) ID {
	h := sha256.Sum256([]byte(data))
	bi := new(big.Int).SetBytes(h[:])
	base := big.NewInt(3)
	mod := new(big.Int)

	var id uint64
	var p uint64 = 1

	for i := 0; i < ID_TRIT_WIDTH; i++ {
		bi.DivMod(bi, base, mod)
		trit := mod.Uint64()
		id += trit * p
		p *= 3
	}
	return ID(id)
}

func calcDist(id1, id2 ID) uint64 {
	var dist uint64
	var p uint64 = 1
	v1, v2 := uint64(id1), uint64(id2)

	for i := 0; i < ID_TRIT_WIDTH; i++ {
		t1 := v1 % 3
		t2 := v2 % 3
		v1 /= 3
		v2 /= 3
		d := (t1 + t2) % 3 // 距离核心算法
		dist += d * p
		p *= 3
	}
	return dist
}

// buildDynamicBackupLinks: 构建基于度约束的动态跨区备份映射
func buildDynamicBackupLinks(regions []Region, nodeNames []string, rttMatrix [][]float64, maxInDegree int) {
	fmt.Printf("\n正在执行跨区域备份动态路由构建 (最大入度约束: %d)...\n", maxInDegree)

	// 1. 选出每个区域的“代表节点” (综合 Bandwidth 和 RAM)
	for i := range regions {
		var bestNode *Node
		var maxScore float64 = -1

		for _, n := range regions[i].Nodes {
			// 打分公式: 带宽(MB) + RAM(GB) * 权重
			score := n.Bandwidth + float64(n.RAM)/(1024*1024*1024)*10.0
			if score > maxScore {
				maxScore = score
				bestNode = n
			}
		}
		regions[i].Representative = bestNode
	}

	// 2. 根据 RTT 和度配额建立映射
	inDegree := make(map[int]int) // 记录每个区域被作为备份目标的次数

	for i := range regions {
		repI := regions[i].Representative

		// 搜集所有候选区域并按 RTT 排序
		type Candidate struct {
			Idx int
			RTT float64
		}
		var candidates []Candidate
		for j := range regions {
			if i == j {
				continue // 不能备份给自己
			}
			repJ := regions[j].Representative
			rtt := getSimulatedRTT(repI.Name, repJ.Name, nodeNames, rttMatrix)
			candidates = append(candidates, Candidate{Idx: regions[j].Index, RTT: rtt})
		}

		// 按 RTT 从小到大排序
		sort.Slice(candidates, func(a, b int) bool {
			return candidates[a].RTT < candidates[b].RTT
		})

		// 贪心选择满足度约束的最优候选者
		selectedIdx := -1
		selectedRTT := 0.0
		for _, cand := range candidates {
			if inDegree[cand.Idx] < maxInDegree {
				selectedIdx = cand.Idx
				selectedRTT = cand.RTT
				inDegree[cand.Idx]++
				break
			}
		}

		// 兜底机制: 如果所有区域的配额都满了 (通常在 maxInDegree 极小且节点极多时发生)
		// 强制选择 RTT 绝对最短的，放宽约束以保证系统连通
		if selectedIdx == -1 {
			selectedIdx = candidates[0].Idx
			selectedRTT = candidates[0].RTT
			inDegree[candidates[0].Idx]++
			fmt.Printf("    [警告] 触发配额兜底，强制映射至 Region %d\n", selectedIdx)
		}

		// 写入映射表
		regions[i].BackupRegionID = selectedIdx
		fmt.Printf(" -> Region %d (代表: %s) 的最优备份区域锁定为 Region %d (代表: %s, RTT: %.2fms)\n",
			regions[i].Index, repI.Name, selectedIdx, regions[selectedIdx].Representative.Name, selectedRTT)
	}
}

// --- 4. 节点文件系统操作 ---

func (n *Node) initNodeStorage() {
	path := filepath.Join(ROOT_STORAGE_DIR, n.Name)
	os.MkdirAll(filepath.Join(path, "data"), 0755) // 存文件内容
	os.MkdirAll(filepath.Join(path, "meta"), 0755) // 存元数据
	n.StoragePath = path
}

func (n *Node) WriteData(fileID ID, content []byte) error {
	filename := fmt.Sprintf("%d.dat", fileID)
	path := filepath.Join(n.StoragePath, "data", filename)
	return ioutil.WriteFile(path, content, 0644)
}

func (n *Node) ReadData(fileID ID) ([]byte, error) {
	filename := fmt.Sprintf("%d.dat", fileID)
	path := filepath.Join(n.StoragePath, "data", filename)
	return ioutil.ReadFile(path)
}

// --- 实验仿真核心逻辑 ---

// 从 RTT 矩阵中查找两个节点间的单向延迟

// Helper: 模拟网络抖动
// 这里我们简单利用 mdev 概念：RTT + 随机偏差
//func getJitteredDelay(baseRTT float64) time.Duration {
// 假设 mdev 是 RTT 的 10% (你可以从 json 读取真实的 mdev)
//	mdev := baseRTT * 0.1
// 简易随机: -mdev 到 +mdev 之间 注意: 真实模拟需要 math/rand 的 NormalFloat64
//jitter := (rand.Float64()*2 - 1) * mdev
//final := (baseRTT / 2) + jitter
//if final < 0 {
//	final = 0
//}
//return time.Duration(final) * time.Millisecond
//}

// 辅助函数：只查表返回 float64 RTT
// 1. 获取基础 RTT (查表)
func getSimulatedRTT(nodeA, nodeB string, nodeNames []string, rttMatrix [][]float64) float64 {
	if nodeA == nodeB {
		return 0.5
	} // 本地回环
	idxA, idxB := -1, -1
	for i, name := range nodeNames {
		if name == nodeA {
			idxA = i
		}
		if name == nodeB {
			idxB = i
		}
	}
	if idxA == -1 || idxB == -1 {
		return 100.0
	} // 默认兜底
	return rttMatrix[idxA][idxB]
}

// --- 9. 物理传输层仿真 (重构版) ---
// 模拟 TCP 连接握手
// 返回: 连接耗时, 错误信息
func connectNode(targetNode *Node, isDead bool) (time.Duration, error) {
	// 模拟 TCP 三次握手 RTT
	// 如果是死节点，客户端不知道，会一直重试直到超时
	const CONNECT_TIMEOUT = 5 * time.Second

	// [解决 Unused] 使用 targetNode 打印日志，模拟真实连接行为
	if targetNode != nil {
		fmt.Printf("      [TCP握手] 正在尝试建立与节点 %s 的连接...\n", targetNode.Name)
	}

	if isDead {
		// 真实情况：发送 SYN，无回音，重试... 直到超时
		time.Sleep(CONNECT_TIMEOUT)
		return CONNECT_TIMEOUT, fmt.Errorf("connection timeout")
	}

	// 活节点：模拟握手耗时 (1.5 RTT)
	// 这里简单给一个握手开销，比如 50ms - 200ms
	handshakeTime := time.Duration(50+rand.IntN(150)) * time.Millisecond
	time.Sleep(handshakeTime)
	return handshakeTime, nil
}

// 用户人为注入的丢包率 (0.0 ~ 1.0)，例如 0.05 代表 5%
var GlobalInjectedLoss float64 = 0.0

// --- 物理传输层仿真 ---
// ReadDataSimulated: 基于数据包的传输模拟 支持人为注入丢包
func (n *Node) ReadDataSimulated(fileID ID, clientLoc string, nodeNames []string, rttMatrix [][]float64, fileSize int64, isSilent bool) (TransferStats, error) {
	stats := TransferStats{}
	start := time.Now()

	// 1. 增加负载 (原子操作)
	currentLoad := atomic.AddInt64(&n.ActiveRequests, 1)
	defer atomic.AddInt64(&n.ActiveRequests, -1)

	// 2. 基础网络参数
	baseRTT := getSimulatedRTT(clientLoc, n.Name, nodeNames, rttMatrix)
	// 假设基础丢包率 (Packet Loss Rate) 与 RTT 正相关 (距离越远越容易丢)
	// 例如: 200ms RTT -> 0.2% 丢包率; 20ms RTT -> 0.02%
	baseLossRate := (baseRTT / 1000.0) * 0.01

	// 3. 定义数据包 (MTU)
	const PACKET_SIZE = 100 * 1024 // 100KB 一个包
	totalPackets := int(math.Ceil(float64(fileSize) / float64(PACKET_SIZE)))
	stats.TotalPackets = totalPackets

	// --- 核心：TCP 流式传输模拟 ---
	// 现实中 1000 个包不是等待 1000 个延迟，而是并发流动的
	// 总延迟分为：首包延迟 + 整体带宽消耗(注释后是会相对快一点点)
	//firstPacketLatency := time.Duration(baseRTT/2) * time.Millisecond
	//time.Sleep(firstPacketLatency) // 模拟握手后的首包到达延迟

	for i := 1; i <= totalPackets; i++ {
		// 动态带宽计算
		efficiency := math.Max(0.4, 1.0-float64(currentLoad-1)*0.1)
		currentBandwidth := (n.Bandwidth / float64(currentLoad)) * efficiency

		packetTime := float64(PACKET_SIZE) / currentBandwidth
		packetDuration := time.Duration(packetTime * 1e9)

		// 1. 计算当前环境丢包率 (基础 + 拥堵惩罚)
		currentNaturalLoss := baseLossRate
		if currentLoad > 3 {
			currentNaturalLoss *= 5.0 // 拥堵惩罚
		}

		// 2. 叠加人为注入的丢包率 (例如 5%)
		totalLossProbability := currentNaturalLoss + GlobalInjectedLoss

		// 3. 判定
		if rand.Float64() < totalLossProbability {
			stats.LostPackets++
			stats.Retransmissions++
			// 惩罚: 丢包导致 TCP 超时重传等待 (RTO)
			time.Sleep(time.Duration(baseRTT*1.5) * time.Millisecond)
		}

		// 这里不再 Sleep(latency)，只 Sleep 带宽消耗的时间
		time.Sleep(packetDuration)
		if !isSilent {
			if i%(totalPackets/10) == 0 || i == totalPackets {
				percent := float64(i) / float64(totalPackets) * 100
				fmt.Printf("\r    [传输进度] %3.0f%% | 已接收: %4d/%d 包", percent, i, totalPackets)
			}
		}
	}
	if !isSilent {
		fmt.Println()
	}
	fmt.Println()
	stats.TotalDuration = time.Since(start)
	stats.ActualBandwidth = float64(fileSize) / stats.TotalDuration.Seconds()

	return stats, nil
}

func (n *Node) WriteMeta(key string, newMeta FileMetadata) error {
	filename := fmt.Sprintf("%s.json", key)
	path := filepath.Join(n.StoragePath, "meta", filename)

	// 1. 读取现有列表
	var metaList []FileMetadata
	bytes, err := ioutil.ReadFile(path)
	if err == nil {
		if len(bytes) > 0 && bytes[0] == '[' {
			json.Unmarshal(bytes, &metaList)
		} else {
			// 兼容旧数据的兜底
			var single FileMetadata
			if json.Unmarshal(bytes, &single) == nil {
				metaList = append(metaList, single)
			}
		}
	}

	// 2. 更新或追加 (Upsert)
	found := false
	for i, existing := range metaList {
		// 如果 ID 相同 (针对 Kill/Recover 更新位置) 或 类型+Owner 相同 (针对 Upload 覆盖)
		// 注意：这里我们主要用 FileID 来判断是否是同一个文件的元数据更新
		if existing.FileID == newMeta.FileID {
			metaList[i] = newMeta // 更新旧记录
			found = true
			break
		}
	}
	if !found {
		metaList = append(metaList, newMeta) // 追加新记录
	}

	// 3. 写回
	newData, _ := json.MarshalIndent(metaList, "", "  ")
	return ioutil.WriteFile(path, newData, 0644)
}

//	ReadMeta: 从列表中筛选正确的文件 ：为了保持接口简单，假设外部调用者如果没传 type，我们就返回列表的第一个（或者报错）
//
// 但为了配合 API_FindAndGet 的逻辑，我们这里做简单适配
func (n *Node) ReadMeta(key string) ([]FileMetadata, error) {
	filename := fmt.Sprintf("%s.json", key)
	path := filepath.Join(n.StoragePath, "meta", filename)
	bytes, err := ioutil.ReadFile(path)
	if err != nil {
		return nil, err
	}

	var metaList []FileMetadata
	if len(bytes) > 0 && bytes[0] == '[' {
		err = json.Unmarshal(bytes, &metaList)
	} else {
		var single FileMetadata
		err = json.Unmarshal(bytes, &single)
		metaList = []FileMetadata{single}
	}
	return metaList, err
}

// --- 3. 辅助功能函数 ---

func findClosestNode(targetID ID, nodes []*Node) *Node {
	var bestNode *Node
	minDist := uint64(math.MaxUint64)

	for _, node := range nodes {
		d := calcDist(targetID, node.ID)
		if d < minDist {
			minDist = d
			bestNode = node
		}
	}
	return bestNode
}

func findClosestNodesInRegion(targetID ID, region Region, n int) []*Node {
	type nodeDist struct {
		n *Node
		d uint64
	}
	var nds []nodeDist
	for _, node := range region.Nodes {
		d := calcDist(targetID, node.ID)
		nds = append(nds, nodeDist{n: node, d: d})
	}
	sort.Slice(nds, func(i, j int) bool { return nds[i].d < nds[j].d })

	count := n
	if len(nds) < count {
		count = len(nds)
	}
	result := make([]*Node, count)
	for i := 0; i < count; i++ {
		result[i] = nds[i].n
	}
	return result
}

// --- 6. API 业务逻辑 (已修改) ---

// API_Upload: 修复了节点选择逻辑
func API_Upload(localFilePath string, fileType string, regions []Region, allNodes []*Node) {
	fmt.Printf("\n[API] 正在上传: %s ...\n", localFilePath)

	// 1. 读取本地源文件
	content, err := ioutil.ReadFile(localFilePath)
	if err != nil {
		fmt.Printf("错误: 无法读取本地文件 %s\n", localFilePath)
		return
	}
	stat, _ := os.Stat(localFilePath)
	fileName := filepath.Base(localFilePath)

	// 2. 准备元数据
	fileID := hashFunc(fileName)
	meta := FileMetadata{
		Name:   fileName,
		Type:   fileType,
		Size:   stat.Size(),
		FileID: fileID,
	}

	// 3. 寻找主区域 (Primary Region)
	nearestRegionID := -1
	minVal := uint64(math.MaxUint64)
	for _, r := range regions {
		if d := calcDist(fileID, r.RegionCenterID); d < minVal {
			minVal = d
			nearestRegionID = r.Index
		}
	}

	// 4. 计算环位置并确定备份区域
	pRegion := regions[nearestRegionID]
	cRegionID := pRegion.BackupRegionID
	cRegion := regions[cRegionID]

	fmt.Printf(" -> 文件主区域: Region %d \n", pRegion.Index)
	fmt.Printf(" -> 跨区域动态备份: Region %d \n", cRegionID)

	// 选择 Primary Node (主区域内距离文件ID最近的两个节点)
	pNodes := findClosestNodesInRegion(fileID, pRegion, 2)
	if len(pNodes) == 0 {
		fmt.Println("错误: 主区域没有可用节点，上传终止。")
		return
	}
	primaryNode := pNodes[0]
	var localBackupNode *Node

	// 如果主区域里有超过1个节点，则第2个作为同区备份
	if len(pNodes) > 1 {
		localBackupNode = pNodes[1]
	}

	// 选择 Backup Node (备份区域内距离文件ID最近的节点)
	cNodes := findClosestNodesInRegion(fileID, cRegion, 1)
	var crossNode *Node
	if len(cNodes) > 0 {
		crossNode = cNodes[0]
	}

	// 更新元数据中的位置信息
	meta.Locations.PrimaryNodeID = primaryNode.ID
	if localBackupNode != nil {
		meta.Locations.BackupNodeID = localBackupNode.ID // 这里存的是同区域备份
	}
	if crossNode != nil {
		meta.Locations.CrossNodeID = crossNode.ID // 这里存的是跨区域备份
	}

	// 执行写入 (Primary)
	fmt.Printf(" -> [1/3] 写入数据到节点: %s (路径: %s/data/%d.dat)\n", primaryNode.Name, primaryNode.Name, fileID)
	if err := primaryNode.WriteData(fileID, content); err != nil {
		fmt.Printf("错误: 写入主节点失败: %v\n", err)
		return
	}

	// 执行写入 (Backup)
	if localBackupNode != nil {
		fmt.Printf(" -> [2/3] 写入数据到节点: %s\n", localBackupNode.Name)
		if err := localBackupNode.WriteData(fileID, content); err != nil {
			fmt.Printf("警告: 备份写入失败: %v\n", err)
			// 备份失败通常不视为上传完全失败，继续执行
		}
	} else {
		fmt.Println(" -> [2/3] 警告: 没有可用的备份区域节点。")
	}

	// 3. 写入跨区域备份节点
	if crossNode != nil {
		fmt.Printf(" -> [3/3] 跨区域备份节点: %s (Region %d)\n", crossNode.Name, cRegion.Index)
		if err := crossNode.WriteData(fileID, content); err != nil {
			fmt.Printf(" 警告: 跨区备份写入失败 %v\n", err)
		}
	} else {
		fmt.Println(" -> [3/3] 警告: 没有可用的备份区域节点。")
	}

	// 8. 写入元数据 (Write Meta)
	// A. ALL Tree
	metaNodeALL := findClosestNode(fileID, allNodes)
	// 这里传入局部变量 meta
	metaNodeALL.WriteMeta(fmt.Sprintf("%d", fileID), meta)
	fmt.Printf(" -> 索引更新 [Global]: 元数据存入 %s\n", metaNodeALL.Name)

	// B. Domain Tree
	domainKeyStr := fileType + ":" + fileName
	domainID := hashFunc(domainKeyStr)
	metaNodeDomain := findClosestNode(domainID, allNodes)
	metaNodeDomain.WriteMeta(fmt.Sprintf("D_%d", domainID), meta)
	fmt.Printf(" -> 索引更新 [Domain]: 元数据存入 %s (Key: %s)\n", metaNodeDomain.Name, domainKeyStr)

	fmt.Println("上传完成。")
}

// --- 6. API 业务逻辑 (修复了提取流程，增加了自动切换备份逻辑，引入超时控制) ---

// --- 6. API 业务逻辑 (完整优化版：支持列表筛选 + 容灾备份 + 故障自动切换) ---

func API_FindAndGet(fileName string, fileType string, allNodes []*Node) {
	fmt.Printf("\n[API] 正在查找文件: %s (Type: %s)...\n", fileName, fileType)

	var targetMeta FileMetadata // 用于存储最终找到的元数据
	metaFound := false          // 标记是否成功找到

	// =========================================================
	// 阶段一：元数据检索 (Metadata Retrieval)
	// =========================================================

	// --- [尝试 1] ALL-Tree (Global Index) ---
	// 逻辑：计算文件名 Hash -> 找到节点 -> 读取列表 -> 筛选匹配 Type 的文件
	globalID := hashFunc(fileName)
	metaNodeGlobal := findClosestNode(globalID, allNodes)

	fmt.Printf(" -> [尝试 1] 查询 Global 索引节点: %s ... ", metaNodeGlobal.Name)

	// 注意：这里假设你已经按上一轮建议修改了 ReadMeta，使其返回 ([]FileMetadata, error)
	metaList, err := metaNodeGlobal.ReadMeta(fmt.Sprintf("%d", globalID))

	if err == nil {
		// 在返回的列表中查找匹配的文件
		for _, m := range metaList {
			// 如果用户未指定类型，默认取第一个；如果指定了类型，必须精确匹配
			if fileType == "" || m.Type == fileType {
				targetMeta = m
				metaFound = true
				fmt.Println("成功 (命中列表)")
				break
			}
		}
		if !metaFound {
			fmt.Println("失败 (节点在线但未找到指定类型的文件)")
		}
	} else {
		fmt.Printf("失败 (节点离线或无数据: %v)\n", err)
	}

	// --- [尝试 2] Domain-Tree (Backup Index) ---
	// 触发条件：Global 尝试失败，且用户提供了 fileType (否则无法计算 Domain Hash)
	if !metaFound && fileType != "" {
		fmt.Printf("    >> [容灾] 触发元数据恢复机制，切换至 Domain 索引...\n")

		// 重新计算 Domain Key: hash(type + ":" + fileName)
		domainKeyStr := fileType + ":" + fileName
		domainID := hashFunc(domainKeyStr)
		metaNodeDomain := findClosestNode(domainID, allNodes)

		fmt.Printf(" -> [尝试 2] 查询 Domain 索引节点: %s (Key: %s) ... ", metaNodeDomain.Name, domainKeyStr)

		// Domain 节点存储的文件名带有 "D_" 前缀
		metaListBackup, errBackup := metaNodeDomain.ReadMeta(fmt.Sprintf("D_%d", domainID))

		if errBackup == nil {
			// 理论上 Domain 节点里的列表应该只有一个文件，但逻辑上保持一致进行遍历
			for _, m := range metaListBackup {
				if m.Type == fileType {
					targetMeta = m
					metaFound = true
					fmt.Println("成功 (从备份索引恢复)")
					break
				}
			}
		} else {
			fmt.Printf("失败 (%v)\n", errBackup)
		}
	}

	// --- 元数据检索结果判定 ---
	if !metaFound {
		fmt.Println("\n[错误] 无法获取文件元数据。可能原因：")
		fmt.Println("  1. 文件不存在")
		fmt.Println("  2. 未指定文件类型 (fileType) 导致无法启动容灾查找")
		fmt.Println("  3. 存储元数据的所有节点(Global & Domain)均已故障")
		return
	}

	// 显示元数据信息
	fmt.Printf("\n    [文件信息] ID: %d | Name: %s | Type: %s | Size: %d\n",
		targetMeta.FileID, targetMeta.Name, targetMeta.Type, targetMeta.Size)
	fmt.Printf("    [存储拓扑] 主: %d | 备1(同区): %d | 备2(跨区): %d\n",
		targetMeta.Locations.PrimaryNodeID, targetMeta.Locations.BackupNodeID, targetMeta.Locations.CrossNodeID)

	// =========================================================
	// 阶段二：文件内容下载 (Data Retrieval with Failover)
	// =========================================================

	// 定义超时时间
	const READ_TIMEOUT = 10 * time.Second

	// 定义待尝试的节点队列 (顺序: 主 -> 同区备 -> 跨区备)
	type TryNode struct {
		Name string
		ID   ID
	}
	targets := []TryNode{
		{"主节点", targetMeta.Locations.PrimaryNodeID},
		{"同区备份", targetMeta.Locations.BackupNodeID},
		{"跨区备份", targetMeta.Locations.CrossNodeID},
	}

	// 辅助查找函数
	findNode := func(id ID) *Node {
		for _, n := range allNodes {
			if n.ID == id {
				return n
			}
		}
		return nil
	}

	var finalData []byte
	success := false

	// 遍历尝试列表
	for _, target := range targets {
		// 跳过无效 ID
		if target.ID == 0 {
			continue
		}

		node := findNode(target.ID)
		if node == nil {
			fmt.Printf(" -> [%s] 节点离线或未找到 (ID: %d)，跳过。\n", target.Name, target.ID)
			continue
		}

		fmt.Printf(" -> [%s] 尝试从 %s 下载 (超时限制: 10s)... ", target.Name, node.Name)

		// --- 异步读取核心逻辑 ---
		type readResult struct {
			data []byte
			err  error
		}
		// 创建缓冲通道防止 goroutine 泄露
		resultChan := make(chan readResult, 1)

		// 启动子协程进行阻塞式读取
		go func(n *Node, fid ID) {
			d, e := n.ReadData(fid)
			resultChan <- readResult{data: d, err: e}
		}(node, targetMeta.FileID)

		// 使用 select 进行超时竞争
		select {
		case res := <-resultChan:
			// 情况 A: 数据在超时前返回
			if res.err == nil {
				fmt.Println("成功!")
				finalData = res.data
				success = true
			} else {
				fmt.Printf("失败 (读取错误: %v)\n", res.err)
			}
		case <-time.After(READ_TIMEOUT):
			// 情况 B: 超时发生
			fmt.Println("失败 (操作超时: >10s)")
		}
		// 如果成功拿到数据，直接跳出循环
		if success {
			break
		}
		fmt.Println("    >> 触发数据节点故障转移，切换至下一节点...")
	}

	// 3. 结果处理
	if !success {
		fmt.Println("错误: 文件提取失败 (所有副本均不可用或超时)。")
		return
	}
	fmt.Printf("成功获取 %d 字节数据。\n", len(finalData))

	// 保存到客户端下载目录
	saveName := fmt.Sprintf("downloaded_%s_%s.%s", targetMeta.Name, time.Now().Format("150405"), targetMeta.Type)
	savePath := filepath.Join(DOWNLOAD_DIR, saveName)
	ioutil.WriteFile(savePath, finalData, 0644)
	fmt.Printf("文件已保存至: %s\n", savePath)
}

// --- 7. 故障模拟与恢复逻辑 (新增) ---

// cmdKillNode: 模拟节点故障，触发数据自动迁移
func cmdKillNode(nodeName string, allNodes []*Node, regions []Region) {
	// 1. 找到目标节点
	var targetNode *Node
	for _, n := range allNodes {
		if n.Name == nodeName {
			targetNode = n
			break
		}
	}
	if targetNode == nil {
		fmt.Printf("错误: 找不到节点 %s\n", nodeName)
		return
	}

	if DeadNodeMap[targetNode.ID] {
		fmt.Printf("节点 %s 已经是故障状态。\n", nodeName)
		return
	}

	// 2. 标记死亡
	DeadNodeMap[targetNode.ID] = true
	fmt.Printf("\n[ALERT] 节点 %s (ID: %d) 发生故障！正在启动容灾迁移程序...\n", targetNode.Name, targetNode.ID)

	// 3. 扫描该节点上的所有文件 (模拟获取受灾文件列表)
	dataPath := filepath.Join(targetNode.StoragePath, "data")
	files, err := ioutil.ReadDir(dataPath)
	if err != nil {
		fmt.Printf("错误: 无法扫描数据目录: %v\n", err)
		return
	}

	// 过滤出 .dat 文件
	var victimFiles []string
	for _, f := range files {
		if !f.IsDir() && strings.HasSuffix(f.Name(), ".dat") {
			victimFiles = append(victimFiles, f.Name())
		}
	}
	totalFiles := len(victimFiles)
	fmt.Printf(" -> 扫描到 %d 个受影响文件，准备迁移。\n", totalFiles)

	if totalFiles == 0 {
		return
	}

	// 4. 定位目标区域 (延迟环上的 Next Region)
	// 4.1 找到当前节点所在的 Region 在环上的位置
	currentRegionIdx := targetNode.RegionIndex
	targetRegionIdx := regions[currentRegionIdx].BackupRegionID
	targetRegion := regions[targetRegionIdx]

	// 5. 计算配额 (向上取整)
	// Limit = Ceil(Total / NodeCount)
	targetNodeCount := len(targetRegion.Nodes)
	if targetNodeCount == 0 {
		fmt.Println("错误: 目标区域没有可用节点，迁移失败。")
		return
	}
	quota := int(math.Ceil(float64(totalFiles) / float64(targetNodeCount)))

	fmt.Printf(" -> 目标区域: Region %d \n", targetRegion)
	fmt.Printf(" -> 均衡策略: 总文件 %d / 节点数 %d = 单节点配额 %d\n", totalFiles, targetNodeCount, quota)

	// 6. 执行迁移
	// 计数器: 记录目标区域每个节点已接收的文件数
	nodeUsage := make(map[ID]int)

	for _, fileName := range victimFiles {
		// 解析 fileID (文件名格式: 12345.dat)
		fidStr := strings.TrimSuffix(fileName, ".dat")
		var fileIDInt uint64
		fmt.Sscanf(fidStr, "%d", &fileIDInt)
		fileID := ID(fileIDInt)

		// A. 读取原始数据 (模拟从故障前的缓存或磁盘残留中读取)
		data, _ := ioutil.ReadFile(filepath.Join(dataPath, fileName))

		// B. 寻找最佳接收节点 (距离优先 + 配额限制)
		//    获取目标区域内节点，按与 fileID 的距离排序
		candidates := findClosestNodesInRegion(fileID, targetRegion, targetNodeCount)

		var selectedNode *Node
		for _, cand := range candidates {
			// 如果该节点存活 且 未满配额
			if isNodeAlive(cand.ID) && nodeUsage[cand.ID] < quota {
				selectedNode = cand
				break
			}
		}

		// 如果所有首选节点都满了(理论上Ceil保证了容量，除非有节点挂了)，选第一个活着的
		if selectedNode == nil {
			for _, cand := range candidates {
				if isNodeAlive(cand.ID) {
					selectedNode = cand
					break
				}
			}
		}

		if selectedNode == nil {
			fmt.Printf("    [Skip] 文件 %d 无法迁移 (目标区域无可用节点)\n", fileID)
			continue
		}

		// C. 物理写入新节点
		nodeUsage[selectedNode.ID]++
		selectedNode.WriteData(fileID, data)

		// D. 更新元数据 (标记 OriginalPrimaryID)
		metaNode := findClosestNode(fileID, allNodes)
		// 1. 读取列表
		metaList, err := metaNode.ReadMeta(fmt.Sprintf("%d", fileID))
		if err != nil {
			fmt.Printf("    [Error] 无法读取文件 %d 的元数据\n", fileID)
			continue
		}

		// 2. 遍历列表找到对应的元数据对象
		var targetMeta FileMetadata
		foundMeta := false
		for _, m := range metaList {
			if m.FileID == fileID {
				targetMeta = m
				foundMeta = true
				break
			}
		}
		if !foundMeta {
			fmt.Printf("    [Error] 元数据列表中未找到 ID 为 %d 的记录\n", fileID)
			continue
		}

		// 3. 修改该对象的 Locations
		targetMeta.Locations.OriginalPrimaryID = targetNode.ID // 记下老家
		targetMeta.Locations.PrimaryNodeID = selectedNode.ID   // 指向新家

		// 4. 写回单个对象 (WriteMeta 会处理更新逻辑)
		metaNode.WriteMeta(fmt.Sprintf("%d", fileID), targetMeta)

		// E. 删除原节点数据 (模拟丢失)
		os.Remove(filepath.Join(dataPath, fileName))
	}

	fmt.Println(" -> 迁移完成。各节点接收统计:")
	for _, n := range targetRegion.Nodes {
		fmt.Printf("    Node %s: %d 个文件\n", n.Name, nodeUsage[n.ID])
	}
}

// 模拟节点恢复，触发数据回迁
func cmdRecoverNode(nodeName string, allNodes []*Node, regions []Region) {
	var recoveredNode *Node
	for _, n := range allNodes {
		if n.Name == nodeName {
			recoveredNode = n
			break
		}
	}
	if recoveredNode == nil {
		fmt.Printf("错误: 找不到节点 %s\n", nodeName)
		return
	}

	if !DeadNodeMap[recoveredNode.ID] {
		fmt.Printf("节点 %s 处于正常状态，无需恢复。\n", nodeName)
		return
	}

	// 2. 标记存活
	delete(DeadNodeMap, recoveredNode.ID)
	fmt.Printf("\n[INFO] 节点 %s (ID: %d) 已重新上线！正在扫描并回迁数据...\n", recoveredNode.Name, recoveredNode.ID)

	// 3. 确定去哪里找数据 (Next Region)
	// Kill 逻辑是将数据移到了环上的 Next Region，所以只需扫描该区域
	currentRegionIdx := recoveredNode.RegionIndex
	targetRegionIdx := regions[currentRegionIdx].BackupRegionID
	targetRegion := regions[targetRegionIdx]

	fmt.Printf(" -> 正在扫描临时托管区域: Region %d\n", targetRegion.Index)

	recoverCount := 0

	// 4. 遍历目标区域的所有节点
	for _, tempNode := range targetRegion.Nodes {
		// 扫描临时节点的数据目录
		tempDataPath := filepath.Join(tempNode.StoragePath, "data")
		files, _ := ioutil.ReadDir(tempDataPath)

		for _, f := range files {
			if f.IsDir() || !strings.HasSuffix(f.Name(), ".dat") {
				continue
			}

			// 解析 FileID
			fidStr := strings.TrimSuffix(f.Name(), ".dat")
			var fileIDInt uint64
			fmt.Sscanf(fidStr, "%d", &fileIDInt)
			fileID := ID(fileIDInt)

			// 5. 检查元数据，确认归属
			metaNode := findClosestNode(fileID, allNodes)
			metaList, err := metaNode.ReadMeta(fmt.Sprintf("%d", fileID)) // 返回的是列表

			if err != nil {
				continue
			}

			// 遍历查找
			var targetMeta FileMetadata
			foundMeta := false
			for _, m := range metaList {
				if m.FileID == fileID {
					targetMeta = m
					foundMeta = true
					break
				}
			}

			// 核心判断: 必须找到元数据，且 OriginalPrimaryID 等于 当前恢复节点的 ID
			if foundMeta && targetMeta.Locations.OriginalPrimaryID == recoveredNode.ID {
				// A. 读回数据
				data, _ := tempNode.ReadData(fileID)

				// B. 写回原节点 (恢复后的节点)
				recoveredNode.WriteData(fileID, data)

				// C. 恢复元数据
				targetMeta.Locations.PrimaryNodeID = recoveredNode.ID
				targetMeta.Locations.OriginalPrimaryID = 0 // 清空标记

				// 写回更新后的单个对象
				metaNode.WriteMeta(fmt.Sprintf("%d", fileID), targetMeta)

				// D. 删除临时副本
				os.Remove(filepath.Join(tempDataPath, f.Name()))
				fmt.Printf("    [回迁] 文件 %d: %s -> %s\n", fileID, tempNode.Name, recoveredNode.Name)
				recoverCount++
			}
		}
	}

	fmt.Printf(" -> 恢复完成。共回迁 %d 个文件。\n", recoverCount)
}

// RunExperiment: 执行三大实验的通用入口
// 参数说明:
//   - targetParam:
//     对于 Exp 1 & 2: 代表文件名 (例如 "test.txt")，用于查找主节点
//     对于 Exp 3:     代表目标节点名 (例如 "Paris")，即由于拥堵的受害者节点
func RunExperiment(expType int, clientLoc string, targetParam string, allNodes []*Node, nodeNames []string, rttMatrix [][]float64) {
	fmt.Printf("\n====== 启动实验 %d (Client: %s) ======\n", expType, clientLoc)

	// 辅助: 按名字找节点
	findNodeByName := func(name string) *Node {
		for _, n := range allNodes {
			if n.Name == name {
				return n
			}
		}
		return nil
	}

	// === 实验 1 (理想) 和 实验 2 (故障切换) 的逻辑 ===
	// --- RunExperiment 的实验二部分逻辑 ---
	// 请将此段逻辑替换 RunExperiment 中 expType == 1 || expType == 2 的原有逻辑

	if expType == 1 || expType == 2 {
		fileName := targetParam
		fmt.Printf(" -> [实验目标] 下载文件: %s\n", fileName)

		// 1. 查找元数据 (模拟 DNS/索引查询)
		fileID := hashFunc(fileName)
		metaNode := findClosestNode(fileID, allNodes)
		metaList, err := metaNode.ReadMeta(fmt.Sprintf("%d", fileID))
		if err != nil || len(metaList) == 0 {
			fmt.Println("错误: 找不到文件元数据 (或列表为空)。")
			return
		}
		targetMeta := metaList[0]

		if len(metaList) > 1 {
			fmt.Printf("    [提示] 发现 %d 个同名文件，默认测试第一个: %s (Type: %s)\n", len(metaList), targetMeta.Name, targetMeta.Type)
		}

		// 2. 构建候选列表 (模拟客户端获取了 Replica List)
		var targets []struct {
			Name string
			ID   ID
			Type string
		}
		if targetMeta.Locations.OriginalPrimaryID != 0 {
			// === 故障模式下的智能顺序 ===
			fmt.Println("    [智能路由] 检测到故障迁移，优先访问同区域备份节点以降低延迟...")
			targets = []struct {
				Name string
				ID   ID
				Type string
			}{
				{"同区备", targetMeta.Locations.BackupNodeID, "LocalBackup (Fastest)"},
				{"新主点", targetMeta.Locations.PrimaryNodeID, "NewPrimary (Migrated)"},
				{"跨区备", targetMeta.Locations.CrossNodeID, "CrossBackup"},
			}
		} else {
			// === 正常模式 ===
			targets = []struct {
				Name string
				ID   ID
				Type string
			}{
				{"主节点", targetMeta.Locations.PrimaryNodeID, "Primary"},
				{"同区备", targetMeta.Locations.BackupNodeID, "LocalBackup"},
				{"跨区备", targetMeta.Locations.CrossNodeID, "CrossBackup"},
			}
		}

		success := false
		startTotal := time.Now()

		// 3. 依次尝试下载 (Failover 循环)
		for _, t := range targets {
			if t.ID == 0 {
				continue
			}

			fmt.Printf(" -> [%s] 正在连接 %s (ID:%d)...\n", t.Type, t.Name, t.ID)

			// 查找节点对象
			var node *Node
			for _, n := range allNodes {
				if n.ID == t.ID {
					node = n
					break
				}
			}

			// === 阶段一: 建立连接 (Handshake) ===
			// 在这里我们不知道节点是否活着，必须试一试
			// isDead 是查询全局 DeadNodeMap 的辅助函数
			isDead := false
			if node == nil || DeadNodeMap[t.ID] {
				isDead = true
			}

			connStart := time.Now()
			_, connErr := connectNode(node, isDead)

			if connErr != nil {
				fmt.Printf("    [连接失败] 耗时: %v | 错误: %v\n", time.Since(connStart), connErr)
				fmt.Println("    >> 触发故障转移，尝试下一节点...")
				continue // 切换到下一个 target
			}

			fmt.Printf("    [连接成功] 握手耗时: %v\n", time.Since(connStart))

			// === 阶段二: 数据传输 (Data Transfer) ===
			fmt.Printf("    [传输中] 正在接收数据包 (Size: 100MB)...\n")

			// 调用新的分包传输函数
			stats, err := node.ReadDataSimulated(targetMeta.FileID, clientLoc, nodeNames, rttMatrix, TEST_FILE_SIZE, false)

			if err != nil {
				fmt.Printf("    [传输中断] %v\n", err)
				continue
			}

			// === 成功 ===
			fmt.Println("    [下载完成]")
			fmt.Printf("    --------------------------------\n")
			fmt.Printf("    | 总耗时      : %v\n", stats.TotalDuration)
			fmt.Printf("    | 总数据包    : %d\n", stats.TotalPackets)
			fmt.Printf("    | 丢包/重传   : %d (丢包率: %.2f%%)\n", stats.LostPackets, float64(stats.LostPackets)/float64(stats.TotalPackets)*100)
			fmt.Printf("    | 实测带宽    : %.2f MB/s\n", stats.ActualBandwidth/1024/1024)
			fmt.Printf("    --------------------------------\n")

			success = true
			break // 成功获取，退出循环
		}

		if success {
			fmt.Printf("\n>>>  成功获取文件 (全流程耗时: %v)\n", time.Since(startTotal))
		} else {
			fmt.Printf("\n>>> 实验失败: 所有节点均不可用\n")
		}
	} else if expType == 3 {
		// === 实验 3 (流量拥堵) 逻辑 ===
		// targetParam 在这里解释为 "Target Node Name" (节点 A)
		targetNodeName := targetParam
		targetNode := findNodeByName(targetNodeName)

		if targetNode == nil {
			fmt.Printf("错误: 找不到目标节点 %s\n", targetNodeName)
			return
		}

		fmt.Printf(" -> 场景: 3个干扰源下载 File A，用户 %s 下载 File B\n", clientLoc)
		fmt.Printf(" -> 目标受拥堵节点: %s (带宽限制: 50MB/s)\n", targetNode.Name)

		// 虚拟文件 ID (仅用于区分)
		fileA_ID := hashFunc("FileA_100M.dat")
		fileB_ID := hashFunc("FileB_100M.dat")

		// 确保目标节点有这俩文件 (写入占位符)
		targetNode.WriteData(fileA_ID, []byte("x"))
		targetNode.WriteData(fileB_ID, []byte("x"))

		// 1. 选取 3 个干扰节点 (J, H, I)
		// 排除 Target 和 Client 自身
		var noiseMakers []string
		count := 0
		for _, name := range nodeNames {
			if name != targetNodeName && name != clientLoc {
				noiseMakers = append(noiseMakers, name)
				count++
				if count == 3 {
					break
				}
			}
		}
		if len(noiseMakers) < 3 {
			fmt.Println("警告: 节点数量不足以产生足够的干扰")
		}

		// 2. 启动背景干扰 (下载 File A)
		stopNoise := make(chan bool)
		var wg sync.WaitGroup

		fmt.Printf(" -> 启动干扰源: %v\n", noiseMakers)
		for _, src := range noiseMakers {
			wg.Add(1)
			go func(noiseSrc string) {
				defer wg.Done()
				for {
					select {
					case <-stopNoise:
						return
					default:
						// 干扰源反复下载 100MB 的 File A
						// 这会占用 targetNode 的 ActiveRequests 计数
						targetNode.ReadDataSimulated(fileA_ID, noiseSrc, nodeNames, rttMatrix, TEST_FILE_SIZE, true)
					}
				}
			}(src)
		}

		// 等待 200ms 确保干扰流已经把带宽占满了
		time.Sleep(200 * time.Millisecond)

		// 3. 执行测试 (用户下载 File B)
		fmt.Printf(" -> 用户 %s 开始下载 File B...\n", clientLoc)
		start := time.Now()

		// 关键: 这里也传 TEST_FILE_SIZE (100MB)
		_, err := targetNode.ReadDataSimulated(fileB_ID, clientLoc, nodeNames, rttMatrix, TEST_FILE_SIZE, false)

		duration := time.Since(start)
		if err == nil {
			fmt.Printf(">>> 拥堵状态下载耗时: %v\n", duration)
		} else {
			fmt.Printf(">>> 下载失败: %v\n", err)
		}

		// 停止干扰
		close(stopNoise)
		// wg.Wait() // 不必等待干扰协程结束，直接返回
	}
}

// --- 分布均匀性测试 ---
func TestDistribution(regions []Region) {
	fmt.Println("\n=== 启动数据分布均匀性测试 (样本: 10000) ===")

	// 计数器
	regionCounts := make(map[int]int)

	for i := 0; i < 10000; i++ {
		// 生成随机文件名
		mockName := fmt.Sprintf("file_%d_%d.dat", i, rand.IntN(9999))
		fileID := hashFunc(mockName)

		// 模拟寻找主区域逻辑
		nearestRegionID := -1
		minVal := uint64(math.MaxUint64)
		for _, r := range regions {
			if d := calcDist(fileID, r.RegionCenterID); d < minVal {
				minVal = d
				nearestRegionID = r.Index
			}
		}
		regionCounts[nearestRegionID]++
	}

	// 打印结果
	fmt.Println("区域负载分布情况:")
	for _, r := range regions {
		count := regionCounts[r.Index]
		percent := float64(count) / 10000.0 * 100
		fmt.Printf("  Region %d: %d (%.2f%%)\n", r.Index, count, percent)
	}
}

// --- 强制均衡辅助函数 ---

// ForceBalanceRegions: 强制将 Region 的中心点 ID 均匀分布在三进制环上
func ForceBalanceRegions(regions []Region) {
	fmt.Println("正在执行 Region 逻辑地址再平衡...")

	// 1. 先按目前的 ID 排序，保持相对顺序不变
	sort.Slice(regions, func(i, j int) bool {
		return regions[i].RegionCenterID < regions[j].RegionCenterID
	})

	// 2. 计算最大 ID 空间
	// 3^27 (27 trits) 约为 7.6 x 10^12
	// 但我们的 hashFunc 生成的是 uint64，为了方便，我们假设空间铺满 uint64
	// 或者严格按照你的三进制逻辑，最大值是 3^27 - 1
	var maxID uint64 = 0
	var p uint64 = 1
	for i := 0; i < ID_TRIT_WIDTH; i++ {
		maxID += 2 * p // 全是 2
		p *= 3
	}

	// 3. 均匀切割
	step := maxID / uint64(len(regions))

	for i := range regions {
		newCenter := uint64(i) * step
		newCenter += step / 2
		fmt.Printf("  Region %d ID 重置: %d -> %d\n", regions[i].Index, regions[i].RegionCenterID, newCenter)
		regions[i].RegionCenterID = ID(newCenter)
		regions[i].Index = i

		for _, node := range regions[i].Nodes {
			node.RegionIndex = i
		}
	}
}

// --- 主程序 ---
func main() {
	//	os.RemoveAll(ROOT_STORAGE_DIR)
	os.MkdirAll(DOWNLOAD_DIR, 0755)

	fmt.Println(" 系统初始化完毕 ")
	nodeNames, rttMatrix := loadRTTData("pingdata-6.json")
	fmt.Printf("成功加载 %d 个节点\n", len(nodeNames))

	var allNodes []*Node
	for _, name := range nodeNames {
		ram := int64((8 + rand.IntN(57)) * 1024 * 1024 * 1024)
		n := &Node{Name: name, ID: hashFunc(name), Bandwidth: NODE_BANDWIDTH, RAM: ram}
		n.initNodeStorage()
		allNodes = append(allNodes, n)
	}
	regions := hierarchicalCluster(rttMatrix, allNodes, N_REGIONS)
	ForceBalanceRegions(regions)
	TestDistribution(regions)

	buildDynamicBackupLinks(regions, nodeNames, rttMatrix, 2)

	fmt.Printf("系统就绪: %d 节点在线, 存储根目录: %s\n", len(allNodes), ROOT_STORAGE_DIR)
	fmt.Println("------------------------------------------------")

	scanner := bufio.NewScanner(os.Stdin)
	for {
		fmt.Print("\n(cli) > ")
		if !scanner.Scan() {
			break
		}
		input := strings.TrimSpace(scanner.Text())
		parts := ParseCommandLine(input)
		if len(parts) == 0 {
			continue
		}

		cmd := parts[0]

		switch cmd {
		case "help":
			fmt.Println("可用命令:")
			fmt.Println("  upload <filepath> <type>  : 上传本地文件 (例如: upload ./test.txt doc)")
			fmt.Println("  get <filename>            : 查找并下载文件 (例如: get test.txt)")
			fmt.Println("  exit                      : 退出系统")

		case "upload":
			if len(parts) < 3 {
				fmt.Println("参数错误。用法: upload <filepath> <type>")
				continue
			}
			path := parts[1]
			ftype := parts[2]

			if _, err := os.Stat(path); os.IsNotExist(err) {
				fmt.Println("[Tip] 文件不存在，正在创建一个测试文件...")
				ioutil.WriteFile(path, []byte("Hello Distributed World! Time: "+time.Now().String()), 0644)
			}

			API_Upload(path, ftype, regions, allNodes)

		case "loss":
			// 用法: loss <percentage>
			// 示例: loss 5  (设置 5% 丢包) ; 示例: loss 0  (清除丢包)
			if len(parts) < 2 {
				fmt.Printf("当前人为丢包率: %.1f%%\n", GlobalInjectedLoss*100)
				fmt.Println("设置用法: loss 5 (表示设置 5% 丢包率)")
				continue
			}

			var rate float64
			fmt.Sscanf(parts[1], "%f", &rate)

			// 限制范围 0~100
			if rate < 0 {
				rate = 0
			}
			if rate > 100 {
				rate = 100
			}

			GlobalInjectedLoss = rate / 100.0
			fmt.Printf(">>> 已设置全局随机丢包率: %.1f%%\n", GlobalInjectedLoss*100)

		case "get":
			if len(parts) < 2 {
				fmt.Println("参数错误。用法: get <filename> [type]")
				fmt.Println("示例: get test.txt (仅查主索引)")
				fmt.Println("示例: get test.txt doc (主索引失败时查备份索引)")
				continue
			}
			fileName := parts[1]
			// 解析可选的 fileType 参数
			fileType := ""
			if len(parts) >= 3 {
				fileType = parts[2]
			}

			// 将 fileType 传入新函数
			API_FindAndGet(fileName, fileType, allNodes)

		case "kill":
			if len(parts) < 2 {
				fmt.Println("参数错误。用法: kill <node_name> (例如: kill Node_01)")
				continue
			}
			// 如果没加引号且被拆分了 (例如 kill Los Angeles)，我们尝试手动拼接
			nodeName := parts[1]
			if len(parts) > 2 {

				nodeName = strings.Join(parts[1:], " ")
			}
			cmdKillNode(nodeName, allNodes, regions)

		case "recover":
			if len(parts) < 2 {
				fmt.Println("参数错误。用法: recover <node_name> (例如: recover Node_01)")
				continue
			}
			nodeName := parts[1]
			if len(parts) > 2 {
				nodeName = strings.Join(parts[1:], " ")
			}
			cmdRecoverNode(nodeName, allNodes, regions)

		case "experiment":
			// 用法: experiment <type 1|2|3> <filename> <client_city>
			// 例如: experiment 1 test.txt Beijing
			if len(parts) < 4 {
				fmt.Println("参数错误: 用法: experiment <1|2|3> <filename> <client_city>")
				fmt.Println("  1: 理想状态测试")
				fmt.Println("  2: 故障切换测试 (请先 kill 主节点)")
				fmt.Println("  3: 流量拥堵测试")
				fmt.Println("建议对于带空格的城市名使用引号包裹。")
				fmt.Println("示例: experiment 3 \"Los Angeles\" \"New York\"")
				continue
			}

			expType := 0
			fmt.Sscanf(parts[1], "%d", &expType)
			targetParam := parts[2]
			clientLoc := parts[3]

			RunExperiment(expType, clientLoc, targetParam, allNodes, nodeNames, rttMatrix)
			fmt.Println("实验结束。")

		case "exit":
			fmt.Println("系统关闭。")
			return

		default:
			fmt.Println("未知命令。输入 'help' 查看帮助。")
		}
	}
}

// hierarchicalCluster 聚类算法
func hierarchicalCluster(rttMatrix [][]float64, nodes []*Node, k int) []Region {
	n := len(nodes)
	clusters := make([]Cluster, n)
	for i := 0; i < n; i++ {
		clusters[i] = Cluster{NodeIndices: []int{i}, Index: i}
	}

	distFn := func(c1, c2 Cluster) float64 {
		sum := 0.0
		count := 0
		for _, u := range c1.NodeIndices {
			for _, v := range c2.NodeIndices {
				sum += rttMatrix[u][v]
				count++
			}
		}
		if count == 0 {
			return math.MaxFloat64
		}
		return sum / float64(count)
	}

	for len(clusters) > k {
		minDist := math.MaxFloat64
		mergeI, mergeJ := -1, -1

		for i := 0; i < len(clusters); i++ {
			for j := i + 1; j < len(clusters); j++ {
				// 约束：如果合并后的簇大小会大于 3，则禁止合并
				if len(clusters[i].NodeIndices)+len(clusters[j].NodeIndices) > 6 {
					continue
				}

				if d := distFn(clusters[i], clusters[j]); d < minDist {
					minDist, mergeI, mergeJ = d, i, j
				}
			}
		}

		if mergeI == -1 || mergeJ == -1 {
			fmt.Println("警告: 聚类算法无法找到满足 size <= 6 约束的合并对，提前终止。")
			break
		}

		clusters[mergeI].NodeIndices = append(clusters[mergeI].NodeIndices, clusters[mergeJ].NodeIndices...)
		clusters = append(clusters[:mergeJ], clusters[mergeJ+1:]...)
	}

	regions := make([]Region, len(clusters))
	for i, c := range clusters {
		rNodes := make([]*Node, len(c.NodeIndices))
		var sumID uint64
		for j, idx := range c.NodeIndices {
			rNodes[j] = nodes[idx]
			rNodes[j].RegionIndex = i
			sumID += uint64(nodes[idx].ID)
		}
		var avgID uint64
		if len(rNodes) > 0 {
			avgID = sumID / uint64(len(rNodes))
		}
		regions[i] = Region{
			Index:          i,
			Nodes:          rNodes,
			RegionCenterID: ID(avgID),
		}
	}
	return regions
}

// --- 算法核心：Region RTT MST -> Hamiltonian Ring ---

// 1. 辅助：计算两个 Region 之间的平均 RTT
func getRegionDist(r1, r2 Region, nameToIdx map[string]int, nodeMatrix [][]float64) float64 {
	sum := 0.0
	count := 0
	for _, n1 := range r1.Nodes {
		u := nameToIdx[n1.Name]
		for _, n2 := range r2.Nodes {
			v := nameToIdx[n2.Name]
			sum += nodeMatrix[u][v]
			count++
		}
	}
	if count == 0 {
		return math.MaxFloat64
	}
	return sum / float64(count)
}

// 2. 核心算法：MST -> Hamiltonian Path -> Ring
func generateMSTRingOrder(regions []Region, nodeNames []string, nodeRTTMatrix [][]float64) []int {
	n := len(regions)
	if n == 0 {
		return []int{}
	}

	// Step A: 构建 Region 级别的 RTT 邻接矩阵 (5x5)
	// 先建立节点名到索引的映射，加速查询
	nameToIdx := make(map[string]int)
	for i, name := range nodeNames {
		nameToIdx[name] = i
	}

	regionDist := make([][]float64, n)
	for i := 0; i < n; i++ {
		regionDist[i] = make([]float64, n)
		for j := 0; j < n; j++ {
			if i == j {
				regionDist[i][j] = 0
			} else {
				regionDist[i][j] = getRegionDist(regions[i], regions[j], nameToIdx, nodeRTTMatrix)
			}
		}
	}

	// Step B: 使用 Prim 算法构建最小生成树 (MST)
	// parent[i] 存储节点 i 在 MST 中的父节点
	parent := make([]int, n)
	key := make([]float64, n) // 记录到达该点的最小权重
	inMST := make([]bool, n)  // 标记是否已加入 MST

	for i := 0; i < n; i++ {
		key[i] = math.MaxFloat64
		inMST[i] = false
	}

	// 从 Region 0 开始构建 MST
	key[0] = 0
	parent[0] = -1

	for count := 0; count < n-1; count++ {
		// 1. 寻找未包含在 MST 中且 key 值最小的节点 u
		min := math.MaxFloat64
		u := -1
		for v := 0; v < n; v++ {
			if !inMST[v] && key[v] < min {
				min = key[v]
				u = v
			}
		}

		if u == -1 {
			break
		}

		// 2. 将 u 加入 MST
		inMST[u] = true

		// 3. 更新 u 的邻接节点
		for v := 0; v < n; v++ {
			// 如果 v 未在 MST 中，且 u-v 的距离小于当前 v 的 key
			if !inMST[v] && regionDist[u][v] != 0 && regionDist[u][v] < key[v] {
				parent[v] = u
				key[v] = regionDist[u][v]
			}
		}
	}

	// 构建 MST 的邻接表表示，方便后续遍历
	mstAdj := make(map[int][]int)
	for i := 1; i < n; i++ {
		p := parent[i]
		// 无向图，添加双向边
		mstAdj[p] = append(mstAdj[p], i)
		mstAdj[i] = append(mstAdj[i], p)
	}

	// 为了保证结果确定性，对邻接表中的子节点排序
	for k := range mstAdj {
		sort.Ints(mstAdj[k])
	}

	// Step C: 将 MST 转换为 Hamiltonian Path (DFS 先序遍历)
	var ringOrder []int
	visited := make([]bool, n)

	var dfs func(u int)
	dfs = func(u int) {
		visited[u] = true
		ringOrder = append(ringOrder, u) // 记录访问顺序

		// 遍历 MST 中的邻居
		for _, v := range mstAdj[u] {
			if !visited[v] {
				dfs(v)
			}
		}
	}

	// 从根节点 (0) 开始遍历
	dfs(0)
	return ringOrder
}

// ParseCommandLine: 解析命令行输入，支持双引号包裹带空格的参数
// 例如: experiment 3 "Los Angeles" "New York" -> ["experiment", "3", "Los Angeles", "New York"]
func ParseCommandLine(input string) []string {
	var args []string
	var current strings.Builder
	inQuote := false

	for _, r := range input {
		switch r {
		case '"':
			inQuote = !inQuote
		case ' ':
			if !inQuote {
				if current.Len() > 0 {
					args = append(args, current.String())
					current.Reset()
				}
			} else {
				current.WriteRune(r)
			}
		default:
			current.WriteRune(r)
		}
	}

	if current.Len() > 0 {
		args = append(args, current.String())
	}

	return args
}
