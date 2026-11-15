/-
Trusted Go model of `golang.org/x/sys/unix` (namespace of the generated package; project bboltfs
of `etc/goose.py`, `Code/golang_org/x/sys/unix.toml`), in terms of the Linux file extension of
`GooseLang.Ext.Fs.Impl` (`Fs.fsExt`), for any program whose extensions include it.
linux/amd64, `golang.org/x/sys` v0.48.0 (`examples/go.mod`).

`unix.Errno` is an alias of `syscall.Errno`, and `errnoErr` boxes it as `syscall`'s does
(`syscall.model.errno`).
-/
module

public import Perennial.Golang.Defn
public import GooseLang.Ext.Fs.Impl
public import LinuxFs.TrustedCode.syscall

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace golang_org.x.sys.unix
section code
variable [GooseExts] [GoGlobalContext]

/-- `Mmap(fd int, offset int64, length int, prot int, flags int) ([]byte, error)`
(`syscall_unix.go`, `mmapper.Mmap`):

```go
	if length <= 0 {
		return nil, EINVAL
	}
	addr, errno := m.mmap(0, uintptr(length), prot, flags, fd, offset)
	if errno != nil {
		return nil, errno
	}
	b := unsafe.Slice((*byte)(unsafe.Pointer(addr)), length)
	p := &b[cap(b)-1]
	m.Lock()
	defer m.Unlock()
	m.active[p] = b
	return b, nil
```

`m.mmap` is `mmap(2)` (the extension's `Mmap`, `(fd, offset, length, prot, flags) ↦ (base,
errno)`, stuck unless the offset is 0, the protection `PROT_READ` and the flags `MAP_SHARED`,
optionally with `MAP_POPULATE`). The slice is built from the base as Go builds it: length and
capacity `length`. The registry `m.active` is not modelled; `Munmap.impl` relies on the
extension's own record of the mappings instead. -/
noncomputable def Mmap.impl : val :=
  λ: "fd" "offset" "length" "prot" "flags",
    if: "length" ≤⟨go.int⟩ #(W64 0) then (#slice.nil, syscall.model.errno #(W64 22)) -- EINVAL
    else
      let: "r" := ExternalOp Fs.fsExt.name "Mmap" ("fd", ("offset", ("length", ("prot", "flags")))) in
      if: Snd "r" ≠⟨go.uintptr⟩ #(W64 0) then (#slice.nil, syscall.model.errno (Snd "r"))
      else
        ((FuncResolve «unsafe».Slice [go.byte, go.int]) #()
          (Convert «unsafe».Pointer (go.PointerType go.byte) (Fst "r")) "length",
         #GoInterface.nil)

/-- `Munmap(b []byte) error` (`syscall_unix.go`, `mmapper.Munmap`):

```go
	if len(data) == 0 || len(data) != cap(data) {
		return EINVAL
	}
	p := &data[cap(data)-1]
	m.Lock()
	defer m.Unlock()
	b := m.active[p]
	if b == nil || &b[0] != &data[0] {
		return EINVAL
	}
	if errno := m.munmap(uintptr(unsafe.Pointer(&b[0])), uintptr(len(b))); errno != nil {
		return errno
	}
	delete(m.active, p)
	return nil
```

The extension's `Munmap` takes the slice's pointer, length and capacity, `(&b[0], len, cap) ↦
errno`, and is stuck unless they are a whole mapping (its base and length), where Go's lookup in
`m.active` returns `EINVAL`: the model is less defined there. For a whole mapping, `b` is
`data` (same first and last bytes). -/
noncomputable def Munmap.impl : val :=
  λ: "b",
    let: "len" := (FuncResolve go.len [go.GoType.SliceType go.byte]) #() "b" in
    let: "cap" := (FuncResolve go.cap [go.GoType.SliceType go.byte]) #() "b" in
    if: ("len" =⟨go.int⟩ #(W64 0)) || ("len" ≠⟨go.int⟩ "cap") then
      syscall.model.errno #(W64 22) -- EINVAL
    else
      syscall.model.errno (ExternalOp Fs.fsExt.name "Munmap"
        (Convert (go.PointerType go.byte) «unsafe».Pointer
          (IndexRef (go.GoType.SliceType go.byte) ("b", #(W64 0))), ("len", "cap")))

/-- `Madvise(b []byte, advice int) error` (`zsyscall_linux.go`: one `madvise(2)`): `nil` or an
arbitrary nonzero `Errno`, with no effect, for the advice values that are only paging hints and
change no byte a load or a read sees: `MADV_NORMAL` (0), `MADV_RANDOM` (1), `MADV_SEQUENTIAL` (2)
and `MADV_WILLNEED` (3). Any other advice is stuck: some change memory (`MADV_DONTNEED` on a
private mapping, `MADV_REMOVE` frees a file's blocks). -/
noncomputable def Madvise.impl : val :=
  λ: "b" "advice",
    if: "advice" ≤⟨go.uint64⟩ #(W64 3) then syscall.model.errno ArbitraryInt
    else Panic "golang.org/x/sys/unix.Madvise: advice not modelled"

/-- `Fallocate(fd int, mode uint32, off int64, len int64) error` (`zsyscall_linux_amd64.go`: one
`fallocate(2)`, `EINTR` not retried). Mode 0 is the extension's `FallocStart`, a truncate to
`max size (off + len)` in flight, and `FallocFinish` (on failure, any size between);
`FALLOC_FL_KEEP_SIZE` (1) is `FallocKeep`, no visible change, any errno
(`notes/walfs-ext-plan.md`). Both are stuck on a negative `off` or a `len` not above 0 (Linux:
`EINVAL`, after the fd's checks: misuse, D6). Other modes (punching or zeroing a range,
collapsing, inserting) are not modelled: a panic, never reached by a proved program. -/
noncomputable def Fallocate.impl : val :=
  λ: "fd" "mode" "off" "len",
    if: "mode" =⟨go.uint32⟩ #(W32 0) then
      syscall.model.errno (ExternalOp Fs.fsExt.name "FallocFinish"
        (ExternalOp Fs.fsExt.name "FallocStart" ("fd", ("off", "len"))))
    else if: "mode" =⟨go.uint32⟩ #(W32 1) then
      syscall.model.errno (ExternalOp Fs.fsExt.name "FallocKeep" ("fd", ("off", "len")))
    else Panic "golang.org/x/sys/unix.Fallocate: mode not modelled"

/-- `unix.Flock_t` as goose names it. -/
@[reducible] def model.Flock_t : go.GoType := go.GoType.Named go!"golang.org/x/sys/unix.Flock_t" []

/-- `FcntlFlock(fd uintptr, cmd int, lk *Flock_t) error` (`fcntl.go`: one `fcntl(2)` with the
lock description `lk`), for `F_OFD_SETLK` (37) and `F_OFD_SETLKW` (38): as `syscall.FcntlFlock`'s
model (`TrustedCode/syscall.lean`, which states the decisions; 2026-11-15, **pending the user's
review**, `notes/wal-units/locks.md`): it loads `Type`, `Whence`, `Start`, `Len`, `Pid`, and a
whole-file request with `Pid` 0 and `Type` `F_RDLCK`, `F_WRLCK` or `F_UNLCK` is the extension's
`OfdLock (fd, (cmd, Type))`, the lock rule on the description's OFD lock; anything else panics (not
modelled). `F_SETLK` (6) and `F_SETLKW` (7), per-process POSIX locks, and any other command (a lock
query, or one that is not about locks at all) are not modelled: a panic, never reached by a proved
program (`examples/osfs/semantics/locks_posix_not_modelled.go`). -/
noncomputable def FcntlFlock.impl : val :=
  λ: "fd" "cmd" "lk",
    if: ("cmd" =⟨go.int⟩ #(W64 37)) || ("cmd" =⟨go.int⟩ #(W64 38)) then
      let: "ty" := ![go.int16] (StructFieldRef model.Flock_t go!"Type" "lk") in
      let: "wh" := ![go.int16] (StructFieldRef model.Flock_t go!"Whence" "lk") in
      let: "st" := ![go.int64] (StructFieldRef model.Flock_t go!"Start" "lk") in
      let: "ln" := ![go.int64] (StructFieldRef model.Flock_t go!"Len" "lk") in
      let: "pid" := ![go.int32] (StructFieldRef model.Flock_t go!"Pid" "lk") in
      if: ("wh" =⟨go.int16⟩ #(W16 0)) && ("st" =⟨go.int64⟩ #(W64 0)) &&
          ("ln" =⟨go.int64⟩ #(W64 0)) && ("pid" =⟨go.int32⟩ #(W32 0)) then
        if: "ty" =⟨go.int16⟩ #(W16 1) then
          syscall.model.errno (ExternalOp Fs.fsExt.name "OfdLock" ("fd", ("cmd", #(W64 1))))
        else if: "ty" =⟨go.int16⟩ #(W16 0) then
          syscall.model.errno (ExternalOp Fs.fsExt.name "OfdLock" ("fd", ("cmd", #(W64 0))))
        else if: "ty" =⟨go.int16⟩ #(W16 2) then
          syscall.model.errno (ExternalOp Fs.fsExt.name "OfdLock" ("fd", ("cmd", #(W64 2))))
        else Panic "golang.org/x/sys/unix.FcntlFlock: a lock type other than F_RDLCK, F_WRLCK, F_UNLCK"
      else Panic "golang.org/x/sys/unix.FcntlFlock: not a whole-file lock with l_pid 0: not modelled"
    else Panic "golang.org/x/sys/unix.FcntlFlock: a command other than F_OFD_SETLK[W] is not modelled"

end code
end golang_org.x.sys.unix

end Perennial
