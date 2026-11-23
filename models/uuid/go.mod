module github.com/google/uuid

// MODEL: v1.3.1's go.mod has no go line and no requirement; the model needs goose's primitive
// (RandomUint64, version4.go) and a go line for it.
go 1.22

require github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
