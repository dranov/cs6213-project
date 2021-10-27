
Results of running the entire model-based testing pipeline + scripts. The test cases are numbered in order of complexity.

The instrumented version of etcd is [here](https://github.com/dariusf/etcd/tree/master/contrib/raftexample).

# Generating traces

You will need [tla2json](https://github.com/japgolly/tla2json/releases/tag/v1.0.1), [TLC](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.1), and Java 14+.

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
