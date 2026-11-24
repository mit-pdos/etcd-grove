/-
Trusted code for etcd's `go.etcd.io/etcd/pkg/v3/runtime` (`pkg/runtime/fds_linux.go`, etcd
`edc800c6f262`), in the generated package's namespace (`Code/go_etcd_io/etcd/pkg/v3/runtime.toml`):
models of `FDUsage` and `FDLimit` (prove-ps2-srvgoroutines, 2026-11-24; Upamanyu's decision (b) on
etcd-grove#42: until then their one caller, etcdserver's `monitorFileDescriptor`, was a names-only
trust-boundary axiom). linux/amd64, Go 1.27.3 (`etc/goose.py`'s `GO_TOOLCHAIN`).

**Why not translated.** `FDUsage` lists procfs's `/proc/self/fd`, and the Linux file extension
(`GooseLang/Ext/Fs`, `TrustedCode/os.lean`) models an ext4 tree with no procfs: its `OpenFile` of a
path outside the tree is not Go's (the real open succeeds). `FDLimit` is `syscall.Getrlimit`, which is
`prlimit1(0, resource, nil, rlim)`, one `RawSyscall6(SYS_PRLIMIT64, ...)` (`zsyscall_linux_amd64.go`),
a system call the repository's `syscall` (`TrustedCode/syscall.lean`) does not model.

**The models are less defined than Go, never more**: each returns any count, or any of the errors Go's
can return (below, per function), with the count Go returns with it. An errno is any nonzero `w64` (a
superset of Linux's errnos), so every `syscall.Errno` Go can produce is among the model's. Neither Go
function panics or blocks (both make one or two system calls, `EINTR` retried by `os`), and neither
touches state the translated code can observe (`FDUsage`'s file is local to `countFiles`, opened and
closed there), so a model that changes nothing is Go's.
-/
module

public import Perennial.Golang.Defn
public import TrustedCode.os
public import TrustedCode.syscall

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace go_etcd_io.etcd.pkg.v3.runtime

noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- The path `FDUsage` lists. -/
abbrev model.procSelfFd : GoString := go!"/proc/self/fd"

/-- `FDUsage() (uint64, error)` (`fds_linux.go`):

```go
func FDUsage() (uint64, error) {
	return countFiles("/proc/self/fd")
}

// countFiles reads the directory named by dirname and returns the count.
func countFiles(dirname string) (uint64, error) {
	f, err := os.Open(dirname)
	if err != nil {
		return 0, err
	}
	list, err := f.Readdirnames(-1)
	f.Close()
	if err != nil {
		return 0, err
	}
	return uint64(len(list)), nil
}
```

Go's outcomes, and the model's:
* success: `(uint64(len(list)), nil)`, some count: the model's `(n, nil)` for any `n`;
* `os.Open` fails: `OpenFile`'s `openFileNolog` returns `&PathError{Op: "open", Path: name, Err: e}`,
  `e` the errno of `openat(2)` (`syscall.Open`'s `errnoErr`, `EINTR` retried: `ignoringEINTR`), and
  `countFiles` `(0, err)`: the model's `(0, &PathError{"open", "/proc/self/fd", Errno(e)})` for any
  nonzero `e`;
* `Readdirnames(-1)` fails: `readdir` (`dir_unix.go`) returns `&PathError{Op: "readdirent", Path:
  f.name, Err: errno}` (`f.name` is the opened name), `errno` the error of `f.pfd.ReadDirent`, and
  `countFiles` `(0, err)` (the names read so far dropped; `Close`'s error ignored): the model's
  `(0, &PathError{"readdirent", "/proc/self/fd", Errno(e)})` for any nonzero `e`. `ReadDirent`'s error
  (`internal/poll/fd_unixjs.go`) is `getdents64(2)`'s errno (`EINTR` retried), or `incref`'s
  `ErrFileClosing` when the file is being closed, or `waitRead`'s error when the fd is pollable and the
  call returned `EAGAIN`: neither happens here, the file being local to `countFiles` and closed only
  after the call, and a directory's fd not pollable (`epoll_ctl(2)` refuses it with `EPERM`, so
  `newFile`'s `pfd.Init` fails, the fd stays unregistered, `pd.pollable()` false, and blocking again;
  `getdents64(2)` on a directory never returns `EAGAIN` anyway); with `readdirName` mode `readdir` makes no other error (its
  `lstat`/dirent errors are of the other modes), and with `n = -1` no `io.EOF`.
`f == nil` (`Readdirnames`'s `ErrInvalid`) does not happen after a successful `Open`. -/
noncomputable def FDUsage.impl : val :=
  λ: <>,
    let: "e" := ArbitraryInt in
    if: "e" =⟨go.uintptr⟩ #(W64 0) then (ArbitraryInt, #GoInterface.nil)
    else
      let: "op" := if: ArbitraryInt =⟨go.uint64⟩ #(W64 0) then #"open" else #"readdirent" in
      (#(W64 0), os.model.pathError "op" #model.procSelfFd (syscall.model.errno "e"))

/-- `FDLimit() (uint64, error)` (`fds_linux.go`):

```go
func FDLimit() (uint64, error) {
	var rlimit syscall.Rlimit
	if err := syscall.Getrlimit(syscall.RLIMIT_NOFILE, &rlimit); err != nil {
		return 0, err
	}
	return rlimit.Cur, nil
}
```

`syscall.Getrlimit(resource, rlim)` is `prlimit1(0, resource, nil, rlim)` (`syscall_linux.go`), whose
body (`zsyscall_linux_amd64.go`) is one `RawSyscall6(SYS_PRLIMIT64, ...)` and `errnoErr(e1)`: `nil`, or
`Errno(e1)` as an `error` (from the preallocated `errEAGAIN`, `errEINVAL`, `errENOENT` for those three,
equal as interface values to the boxed `Errno`). Go's outcomes: `(rlimit.Cur, nil)`, the soft limit
the kernel wrote, any `uint64` (`RLIM_INFINITY` among them): the model's `(n, nil)` for any `n`; and
`(0, Errno(e))` for the call's nonzero errno: the model's, for any nonzero `e`. -/
noncomputable def FDLimit.impl : val :=
  λ: <>,
    let: "e" := ArbitraryInt in
    if: "e" =⟨go.uintptr⟩ #(W64 0) then (ArbitraryInt, #GoInterface.nil)
    else (#(W64 0), syscall.model.errno "e")

end code
end

end go_etcd_io.etcd.pkg.v3.runtime

end Perennial
