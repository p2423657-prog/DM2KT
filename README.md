The project is implemented in the Go programming language and is compiled using Go version 1.24.0.

1. `replication_service.go` is the primary entry point and core service implementation file of the project.

2. Files such as `go.mod` are configuration and dependency management files used to define module metadata and external package requirements.

3. The `.json` files store inter-node RTT (Round-Trip Time) measurement data.

4. Before the initial execution, the `client downloads` and `network storage` directories must be deleted. These directories are auto-generated based on node configuration data and are used in the simulation environment to represent file storage and upload distribution across corresponding nodes.

5.All other files with extensions such as `.bat` or `.txt` are test artifacts used to simulate file uploads from users in different geographic regions and to evaluate how different file types are partitioned within the domain tree structure. Users may also create additional files independently for testing purposes.

The comparative experiments with IPFS were conducted by deploying IPFS nodes via Docker and performing file upload and download tests using basic command-line operations. Due to hardware constraints, automated scripting was not implemented for batch testing. However, the experimental commands are straightforward, and the detailed procedures are thoroughly documented in the paper. By consulting publicly available command-line references, the IPFS experiments can be fully reproduced.

The DM2KT system provides exposed API interfaces and can be executed directly by running the corresponding Go file. The related experimental modules are integrated within the same Go implementation. Specific testing procedures can be examined through the associated command-line instructions.

After successfully launching the system, users can upload files using the `upload` command. The system will automatically determine the appropriate storage nodes based on its allocation strategy and return detailed storage metadata to the user.

To conduct the three predefined experimental evaluations, users may invoke `experiment 1`, `experiment 2`, or `experiment 3` respectively. The system will then activate the corresponding experimental workflow and provide the relevant command-line prompts for execution.
