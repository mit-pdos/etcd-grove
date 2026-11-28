// The Go model of the standard library's syscall (Code/syscall.toml's [model] table, over the Linux
// file extension fsExt's primitive stubs): files of package syscall, spliced into the real package
// by goose (`goose model-overlay` for go build/test). This module is never built; it keeps the files
// out of models.lab's `./...`, where they would not compile as a package of their own path.
module models.lab/stdmodels/syscall

go 1.27
