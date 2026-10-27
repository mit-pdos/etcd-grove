/-
Trusted Go model of `github.com/mit-pdos/etcd-grove/examples/durable` (namespace of the
generated package), in terms of the durable-state extension of `GooseLang.Ext.Durable.Impl`
(`durableExt` and its operations `DurableOp.*`), for any program whose extensions include it.

The Go functions are primitives: `Read(name string) (string, bool)` and
`Write(name, data string)`, whole-file operations on a durable filesystem. What is trusted is
the operating system's file API (`os.ReadFile`, `os.CreateTemp`, `File.Sync`, `os.Rename`,
...), which goose leaves axiomatized, together with the claim that the Go implementation
composes it into atomic, durable whole-file operations: the operations hold a package mutex,
so that no `Read` sees a `Write` before it is durable; a `Write` writes a fresh temporary file
in the file's directory, syncs it, renames it over the file and syncs the directory; a failed
operation is retried, never reported; and a `Read` of a file that does not exist
(`os.ReadFile` failing with `fs.ErrNotExist`) returns `("", false)`. A Go string is a value
(`#s`), as the extension's operations take and return; a `Read`'s two results are a pair, as
goose returns them.

The model departs from Go only by being less defined, where Go keeps retrying forever (a
persistent I/O error, a missing directory) and the model succeeds; as a safety model, it only
needs to cover the executions in which the Go operation returns. The temporary files a `Write`
interrupted by a crash leaves behind are not in the model. The other divergences from a real
filesystem are listed in `GooseLang/Ext/Durable/Impl.lean`.
-/
module

public import Perennial.Golang.Defn
public import GooseLang.Ext.Durable.Impl

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace github_com.mit_pdos.etcd_grove.examples.durable
section durable
variable [GooseExts] [GoGlobalContext]

/-- Type: func(string) (string, bool) -/
def Read.impl : val :=
  λ: "name", ExternalOp (extOp durableExt DurableOp.ReadOp) "name"

/-- Type: func(string, string) -/
def Write.impl : val :=
  λ: "name" "data", ExternalOp (extOp durableExt DurableOp.WriteOp) ("name", "data")

end durable
end github_com.mit_pdos.etcd_grove.examples.durable

end Perennial
