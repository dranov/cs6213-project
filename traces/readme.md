
Results of running the entire model-based testing pipeline + scripts. The test cases are numbered in order of complexity.

# Setup

Install all the prerequisites of the [interpreter](https://github.com/dariusf/etcd/tree/master/contrib/raftexample) and build it.

Make a copy of `env.sh` and modify it accordingly.

```sh
cp env.example.sh env.sh
# modify env.sh
```

Execute `run.sh` from one of these directories. You will probably need to modify `tla/raft.cfg` as the readme of each directory shows.

```sh
cd 01-first-leader
# check readme and modify tla/raft.cfg
../run.sh
```
