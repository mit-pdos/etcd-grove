// The uuid model's difftest against the lab's model (harness/rpcmodel/uuid), substituted as a kit
// substitutes it (a replace); go.mod is the same tests against the real v1.3.1 (run.sh).
module dsverify.lab/uuiddifftest

go 1.22

require github.com/google/uuid v1.3.1

require github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65 // indirect

replace github.com/google/uuid => ../../uuid
