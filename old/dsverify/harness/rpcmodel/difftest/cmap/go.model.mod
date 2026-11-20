// The concurrent-map model's difftest against the lab's model (harness/rpcmodel/cmap), substituted
// as a kit substitutes it (a replace); go.mod is the same tests against the real v1.0.0 (run.sh).
module dsverify.lab/cmapdifftest

go 1.22

require github.com/orcaman/concurrent-map v1.0.0

replace github.com/orcaman/concurrent-map => ../../cmap
