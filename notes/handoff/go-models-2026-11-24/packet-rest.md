# Go-model overlays, rest slice (fmt, log, os/syscall/durable, net, crc32, go/token): review packet (perennial#692)

For Upamanyu's review; nothing here lands without it. The basic slice (sync, internal/sync, time, runtime,
bytealg) is reviewed separately (`goose-model-overlay-basic`, `go-models-basic/2026-11-24`) and is left out:
once it lands on lean, lean is merged into the branches below and this packet shrinks to what follows.

| repo | branch | head | state |
|---|---|---|---|
| Perennial | `goose-model-overlay-rest` | `d81d2bfd8` | whole library + PerennialMeta built (int-full10, EXIT 0); `etc/model-tests.sh` passes; log = lean's |
| etcd-grove | `go-models-rest-egnet/2026-11-24` | `16e82ffff7` (+ notes) | **the packet's branch**: os/syscall/durable/crc32/go-token + net, pinned to the Perennial head above; **all default targets built, EXIT 0**; tcb-report identical to lean's (Evidence) |
| etcd-grove | `go-models-rest/2026-11-24` | `25ff765af9` | the same without net (egnet merged it); the 2026-11-25 review fixes to os are on the egnet branch only (merge egnet, or cherry-pick `d2fa9c8519`, when landing main alone) |

**Decided (coordinator-E, etcd-grove#8 7153952113 / 7166757537), applied 2026-11-25 (session 10):**
- **`log.Println`/`Printf`: trusted exactly as on lean** (Perennial `d81d2bfd8`: log's toml, TrustedCode,
  Code, GeneratedProof, Spec, Proof are lean's byte for byte; log's Go model deleted; fmt's `pp.doPrintln`
  model and `fmt.Fprintln.spec` stay). No trusted text vs lean. Net's `log.Println.spec`/proof are back
  (etcd-grove `c617de6bf3`), so swiftpaxos `SyncTail` proves again. Lean's gap (the no-op does not call
  the arguments' `String`/`Error`/`Format`) is analysed in "The `log.Println` gap" below: **no proved
  path passes such an argument**. Retirement plan: once reflection S0+S0.5 is approved, fmt's model
  printer follows maps over the reflect models; `log.Println`/`Printf` then become the Go model again
  (over `fmt.Fprintln`/`Fprintf`, as at Perennial `30102d8b2`).
- **runtime initializer: (a) not cheap, (b) done.** Proving `runtime`'s initializer means translating or
  modelling 94 names-only runtime variable initializers and 9 `init` functions (`findfunc`/`funcMaxSPDelta`
  over the pclntab, cpu flags, `lockInit`, `go forcegchelper()`, `unsafe.Sizeof` checks), plus
  internal/runtime/sys's 3; the basic slice's runtime models (Version/Caller/Callers/Frames.Next) cover
  none of it. (b), etcd-grove `4313327873`: `os` no longer imports `runtime`. The only translated os
  code calling `runtime.KeepAlive` was `rawConn.Control/Read/Write` (Go's bodies over `poll.FD.Raw*`,
  names-only, so no proof could pass them); they are names-only now (lean: trusted, panicking), and
  goose drops `Process` (field `cleanup runtime.Cleanup`) to an opaque type, as on lean. **No Go model
  and no trusted text were needed**: the "model of KeepAlive/Cleanup" reduces to not translating the
  three methods. The review of (b) found no divergence. tcb-report after = before (Evidence): runtime axioms at
  11 roots again, the 30 results at their lean axiom sets, `raft_kvdurable_porcupine_robust` at 0.

## How to read this packet (your format)

The main content is the list of `MODEL:` deviations, each a unified diff from the real Go declaration
(go1.26.11 for Perennial, go1.27.3 for etcd-grove; linux/amd64, `netgo` files only) to the model that
replaces it, generated from the sources (every name in a `.toml`'s `[model] replaces`; generator
`tmp/gomodels/s4/modeldiff.py`). Everything not listed is Go's source verbatim (translated and verified).
After the diffs: statement changes, decisions to check, open items, reviews, the criterion-14 audit, evidence.

`MODEL:` markers per package (Perennial's `etc/model-deviations.py` from the basic slice's branch, run over
`goose/model/overlay` of `goose-model-overlay-rest` and etcd-grove's `models/`; this packet's packages only):

| package | `MODEL:` markers | model lines (non-test) | replaced declarations |
|---|---:|---:|---|
| fmt (Perennial) | 5 | 843 | `errorf`, `Fprintf`, `pp.doPrint`, `pp.doPrintln` (+ the model printer `printmodel.go`) |
| log (Perennial) | 3 | 69 | `Printf`, `Println`, `init.0` |
| syscall (Perennial) | 1 | 34 | `prlimit1` |
| os (etcd-grove) | 19 | 1147 | `file`, `OpenFile`, `File.{Close,ReadAt,WriteAt,Seek,Write,Read,Stat,Truncate,Sync,Readdirnames,copyFileRange}`, `Rename`, `Stat`, `Lstat`, `RemoveAll` |
| syscall (etcd-grove) | 9 | 237 | `errnoErr`, `init.0`, `Fdatasync`, `Flock`, `Fallocate`, `FcntlFlock`, `Mkdir`, `Unlink`, `Rmdir` |
| durable (etcd-grove) | 2 | 50 | `Read`, `Write` |
| hash/crc32 | 3 | 41 | the three arch hooks |
| go/token | 1 | 37 | `IsExported` |
| net (etcd-grove) | 20 | 435 | `netFD.{Read,Write,Close,closeWrite,SetDeadline,SetReadDeadline,SetWriteDeadline,accept}`, the six sockopt setters, `TCPListener.{accept,close}`, `Listen`, `Dial`, `DialTimeout`, `TCPAddr.String` |
| **total** | **63** | | |

**Open item to flag yourself: size.** fmt's model printer (`printmodel.go`, 691 lines) and os's model (1147
lines) are not "few and small" MODEL sites. fmt: the real printer reaches `printValue`/reflection; the model
printer follows Go's control flow (which user methods are called, in which order, with Go's buffer aliasing)
and writes arbitrary bytes where Go formats. os: the file extension's operations sit below the syscall layer
Go's `os` uses (`poll.FD`; the `ignoringEINTR` loops are translated where possible: Mkdir, Remove, MkdirAll,
`fd`, `readFrom` are real Go). Shrinking either is future work; say if you want it before landing.

# The `MODEL:` deviations


## fmt (Perennial)

#### `Perennial/Code/fmt.toml` — model `goose/model/overlay/fmt`, 4 replaced declarations

##### `errorf`
```diff
--- go
+++ model
@@ -1,4 +1,14 @@
-// errors.go
-// errorf formats and returns an error value, or nil if no formatting is required.
+// print.go
+// MODEL: errorf is Go's, but for its printer: Go's p.doPrintf(format, a), with p.wrapErrs set, is
+// the model printer's doPrintf(&p.buf, format, a, true), which appends the message to p.buf (Go's,
+// with arbitrary strings from the first directive it does not format) and gives the indices of the
+// %w arguments (or that they are unknown); errorfResult builds the error from them as Go's switch
+// on len(p.wrappedErrs) does: errors.New, a *wrapError, a *wrapErrors (see the file comment for
+// what the model printer covers and where it is stuck; TestModelErrorf compares the error's kind,
+// message and wrapped errors with Go's). The printer is Go's own, from newPrinter and back to the
+// pool with p.free(), and the message is read back from p.buf as Go reads it: the pool is
+// observable outside fmt, since Fprintf hands p.buf to a writer, which may keep the slice and see
+// what a later errorf writes into the same printer's buffer, or write into it itself
+// (TestModelAlias, goose/model/fmt).
 func errorf(format string, a ...any) error {
 	if len(a) == 0 && stringslite.IndexByte(format, '%') == -1 {
@@ -6,30 +16,7 @@
 	}
 	p := newPrinter()
-	p.wrapErrs = true
-	p.doPrintf(format, a)
+	wrapped, unknown := doPrintf(&p.buf, format, a, true)
 	s := string(p.buf)
-	var err error
-	switch len(p.wrappedErrs) {
-	case 0:
-		err = errors.New(s)
-	case 1:
-		w := &wrapError{msg: s}
-		w.err, _ = a[p.wrappedErrs[0]].(error)
-		err = w
-	default:
-		if p.reordered {
-			slices.Sort(p.wrappedErrs)
-		}
-		var errs []error
-		for i, argNum := range p.wrappedErrs {
-			if i > 0 && p.wrappedErrs[i-1] == argNum {
-				continue
-			}
-			if e, ok := a[argNum].(error); ok {
-				errs = append(errs, e)
-			}
-		}
-		err = &wrapErrors{s, errs}
-	}
+	err := errorfResult(s, wrapped, unknown, a)
 	p.free()
 	return err
```

##### `Fprintf`
```diff
--- go
+++ model
@@ -1,8 +1,13 @@
 // print.go
-// Fprintf formats according to a format specifier and writes to w.
-// It returns the number of bytes written and any write error encountered.
+// MODEL: Fprintf is Go's, but for one line: Go's p.doPrintf(format, a) is the model printer's
+// doPrintf(&p.buf, format, a, false), which appends to p.buf what Go appends up to its first
+// method call or directive the model does not format, and arbitrary strings from there, before
+// each method call and at the end (see the file comment for what the model printer covers and
+// where it is stuck; TestModelFprintf checks the bytes Write receives and the methods called;
+// TestModelAlias a method reading p.buf through a slice an earlier Write kept). The printer, its
+// pool (ppFree), the one w.Write(p.buf) and p.free() are Go's own.
 func Fprintf(w io.Writer, format string, a ...any) (n int, err error) {
 	p := newPrinter()
-	p.doPrintf(format, a)
+	doPrintf(&p.buf, format, a, false)
 	n, err = w.Write(p.buf)
 	p.free()
```

##### `pp.doPrint`
```diff
--- go
+++ model
@@ -1,13 +1,17 @@
 // print.go
+// MODEL: pp.doPrint prints the operands under %v, a space between two that are not strings. Go
+// tells a string by reflect.TypeOf(arg).Kind() == reflect.String (reflection, which is stuck) and
+// prints each with p.printArg, which is stuck on the operands of the file comment; Fprint's spec
+// admits them (fmt.printArgOk). The model calls of each operand what Go's printArg calls under %v
+// (visitArg: its Error() or String(), stuck where the model printer is), after appending arbitrary
+// strings to p.buf (writeArbitrary), which stand for what Go has appended by then (a method may
+// read p.buf through a slice a writer kept), and appends arbitrary strings at the end, for the
+// rest of Go's output (TestModelFprint checks the calls, TestModelAlias the buffer). Fprint and
+// Sprint, Go's own, print with it.
 func (p *pp) doPrint(a []any) {
-	prevString := false
-	for argNum, arg := range a {
-		isString := arg != nil && reflect.TypeOf(arg).Kind() == reflect.String
-		// Add a space between two non-string arguments.
-		if argNum > 0 && !isString && !prevString {
-			p.buf.writeByte(' ')
-		}
-		p.printArg(arg, 'v')
-		prevString = isString
+	for _, x := range a {
+		writeArbitrary(&p.buf)
+		visitArg(x, 'v', false, false)
 	}
+	writeArbitrary(&p.buf)
 }
```

##### `pp.doPrintln`
```diff
--- go
+++ model
@@ -1,12 +1,14 @@
 // print.go
-// doPrintln is like doPrint but always adds a space between arguments
-// and a newline after the last argument.
+// MODEL: pp.doPrintln is doPrint's model (see there): Go's doPrintln, for each operand, appends a
+// space if it is not the first and prints it with p.printArg(arg, 'v'), then appends '\n'; the
+// model calls of each operand what printArg calls under %v (visitArg), after arbitrary strings
+// (writeArbitrary), which cover Go's space and what printArg appended before, and ends with
+// arbitrary strings, which cover the rest and the newline (TestModelFprintln checks the calls).
+// Fprintln and Sprintln, Go's own, print with it.
 func (p *pp) doPrintln(a []any) {
-	for argNum, arg := range a {
-		if argNum > 0 {
-			p.buf.writeByte(' ')
-		}
-		p.printArg(arg, 'v')
+	for _, x := range a {
+		writeArbitrary(&p.buf)
+		visitArg(x, 'v', false, false)
 	}
-	p.buf.writeByte('\n')
+	writeArbitrary(&p.buf)
 }
```

Model-only declarations (additions, stubs; no real counterpart is replaced): `allInert`, `anyIntArg`, `callError`, `callString`, `chooseString`, `decBytes`, `doPrintf`, `errorfResult`, `formatArg`, `formatHex`, `formatInt`, `formatSlice`, `hasFmtMethod`, `hexBytes`, `hexNibble`, `inert`, `intArg`, `intVerb`, `isBasic`, `isIntKind`, `isStrKind`, `joinStrings`, `kindIs`, `namedIntArg`, `notModelled`, `parseDirective`, `printfFormat`, `quoteByte`, `quoteBytes`, `strArg`, `underlyingAs`, `visitArg`, `visitKind`, `visitRest`, `writeArbitrary`



## log (Perennial)

#### `Perennial/Code/log.toml` — model `goose/model/overlay/log`, 3 replaced declarations

##### `Printf`
```diff
--- go
+++ model
@@ -1,8 +1,33 @@
 // log.go
-// Printf calls Output to print to the standard logger.
-// Arguments are handled in the manner of [fmt.Printf].
+// MODEL: Printf is std.output(0, 2, func(b []byte) []byte { return
+// fmt.Appendf(b, format, v...) }). The standard logger std is not translated
+// (its initializer is New(os.Stderr, "", LstdFlags), and os.Stderr is not a
+// File in the model: perennial#663), nor is any function that changes it
+// (SetOutput, SetFlags, SetPrefix, Default, Logger's setters), so in every
+// execution of the model std is as New made it: flags LstdFlags, no prefix,
+// output os.Stderr. Its output method then:
+//   - returns at once if the output is io.Discard (l.isDiscard), which needs
+//     a SetOutput no execution reaches; the model has both outcomes anyway
+//     (gomodel.Choose: it formats or does nothing);
+//   - reads the clock (time.Now), the prefix and the flags (atomic loads), and
+//     with LstdFlags not the caller's file and line: no effect;
+//   - takes a buffer from bufferPool, formats the date and time into it, and
+//     calls the closure, which formats the arguments as fmt.Appendf does:
+//     fmt's printer and doPrintf, which call the arguments' Error, String and
+//     Format methods, the only effects on the program. The model formats them
+//     with fmt.Fprintf, which runs the same newPrinter, doPrintf and free;
+//   - appends a newline, takes std.outMu (held only by output, never while
+//     the arguments' methods run) and writes the bytes to standard error,
+//     ignoring the result: an effect outside the program, which the model
+//     drops, as it drops Fprintf's bytes (modelDiscard). The write can also
+//     block (a full stderr pipe, holding std.outMu) or end the process
+//     (EPIPE on fd 2: os.File.Write's epipecheck raises SIGPIPE): both stop
+//     the program there, so their traces are prefixes of the model's, which
+//     returns (partial correctness, as for an exit).
+//
+// Neither can panic other than through the arguments' methods.
 func Printf(format string, v ...any) {
-	std.output(0, 2, func(b []byte) []byte {
-		return fmt.Appendf(b, format, v...)
-	})
+	if gomodel.Choose() {
+		fmt.Fprintf(modelDiscard{}, format, v...)
+	}
 }
```

##### `Println`
```diff
--- go
+++ model
@@ -1,8 +1,9 @@
 // log.go
-// Println calls Output to print to the standard logger.
-// Arguments are handled in the manner of [fmt.Println].
+// MODEL: Println is Printf's model (see there) with fmt.Appendln(b, v...) in
+// place of Appendf: the model formats the arguments with fmt.Fprintln, which
+// runs the same newPrinter, doPrintln and free.
 func Println(v ...any) {
-	std.output(0, 2, func(b []byte) []byte {
-		return fmt.Appendln(b, v...)
-	})
+	if gomodel.Choose() {
+		fmt.Fprintln(modelDiscard{}, v...)
+	}
 }
```

##### `init.0`
```diff
--- go
+++ model
@@ -1,8 +1,9 @@
 // log.go
+// MODEL: log's init function stores a closure into
+// log/internal.DefaultOutput, the output of log/slog's default handler; it
+// cannot panic. log/slog and log/internal are not translated, so no execution
+// of the model reads that variable, and the model does nothing.
+//
+//gomodel:replace init.0 "internal.DefaultOutput = func(pc uintptr, data []byte) error {"
 func init() {
-	internal.DefaultOutput = func(pc uintptr, data []byte) error {
-		return std.output(pc, 0, func(buf []byte) []byte {
-			return append(buf, data...)
-		})
-	}
 }
```

Model-only declarations (additions, stubs; no real counterpart is replaced): `init`, `modelDiscard`, `modelDiscard.Write`



## syscall (Perennial)

#### `Perennial/Code/syscall.toml` — model `goose/model/overlay/syscall`, 1 replaced declarations

##### `prlimit1`
```diff
--- go
+++ model
@@ -1,5 +1,24 @@
-// zsyscall_linux_amd64.go
+// prlimit.go
+// MODEL: prlimit1 is the prlimit64 system call: Go's body is
+// RawSyscall6(SYS_PRLIMIT64, uintptr(pid), uintptr(resource),
+// uintptr(unsafe.Pointer(newlimit)), uintptr(unsafe.Pointer(old)), 0, 0) and,
+// for a non-zero errno, errnoErr(e1). The conversions of pointers to uintptr
+// and the system call (assembly) have no semantics. The kernel reads
+// *newlimit if newlimit is non-nil, writes *old if old is non-nil and the call
+// succeeds, and returns 0 or an errno; it cannot fault on Go's pointers and
+// cannot panic. The model reads *newlimit (so a concurrent write races, as
+// with the kernel's read), may write arbitrary limits to *old (a superset of
+// the kernel's writes: always on success, never on failure), and returns
+// errnoErr of an arbitrary errno, nil for 0, as Go's stub does with the
+// kernel's. The limits themselves, the process's state, are not modelled.
 func prlimit1(pid int, resource int, newlimit *Rlimit, old *Rlimit) (err error) {
-	_, _, e1 := RawSyscall6(SYS_PRLIMIT64, uintptr(pid), uintptr(resource), uintptr(unsafe.Pointer(newlimit)), uintptr(unsafe.Pointer(old)), 0, 0)
+	if newlimit != nil {
+		_ = *newlimit
+	}
+	if old != nil && gomodel.Choose() {
+		old.Cur = gomodel.ChooseUint64()
+		old.Max = gomodel.ChooseUint64()
+	}
+	e1 := Errno(gomodel.ChooseUint64())
 	if e1 != 0 {
 		err = errnoErr(e1)
```



## os (etcd-grove)

#### `Code/os.toml` — model `models/os`, 17 replaced declarations

##### `file`
```diff
--- go
+++ model
@@ -1,7 +1,8 @@
-// file_unix.go
-// file is the real representation of *File.
-// The extra level of indirection ensures that no clients of os
-// can overwrite this data, which could cause the finalizer
-// to close the wrong file descriptor.
+// model.go
+// MODEL: file is Go's layout (file_unix.go) with one field added, off, the kernel's file offset of
+// the fd's open file description (f_pos), which Go does not keep and the extension, whose reads and
+// writes name their offsets, does not either. An unexported field of an unexported type: no code
+// outside os can observe it (reflection and unsafe are not modelled), and inside os only the models
+// read or write it.
 type file struct {
 	pfd         poll.FD
@@ -12,3 +13,4 @@
 	appendMode  bool                    // whether file is opened for appending
 	inRoot      bool                    // whether file is opened in a Root
+	off         int64                   // MODEL: the kernel's file offset (f_pos)
 }
```

##### `OpenFile`
```diff
--- go
+++ model
@@ -1,18 +1,28 @@
-// file.go
-// OpenFile is the generalized open call; most users will use Open
-// or Create instead. It opens the named file with specified flag
-// ([O_RDONLY] etc.). If the file does not exist, and the [O_CREATE] flag
-// is passed, it is created with mode perm (before umask);
-// the containing directory must exist. If successful,
-// methods on the returned File can be used for I/O.
-// If there is an error, it will be of type [*PathError].
+// model.go
+// MODEL: OpenFile (file.go, file_unix.go's openFileNolog and newFile). Go's body is
+// `testlog.Open(name)` (a no-op outside go test's logging), then open(2) of name with
+// flag|O_CLOEXEC (O_LARGEFILE is 0 on amd64), EINTR retried, an error being
+// &PathError{"open", name, Errno(e)}, then newFile, whose other work (an fstat deciding whether the
+// fd is pollable, the poller's registration) no Go code observes. NOT COVERED (as on lean, a
+// framework gap: GooseLang has no garbage collection): newFile's finalizer, which closes the fd of
+// a *File that becomes unreachable without Close (releasing its flock locks, freeing the fd
+// number); the model's fd stays open. appendMode is
+// flag&O_APPEND, false since the extension refuses O_APPEND. fsOpen is the extension's Open after its
+// own CallBegin, each attempt. perm matters only to a created file's mode, which the extension does
+// not model. A name with a NUL byte (Go: EINVAL without a system call) is not a path of the roots'
+// trees: the extension is stuck on it.
 func OpenFile(name string, flag int, perm FileMode) (*File, error) {
-	testlog.Open(name)
-	f, err := openFileNolog(name, flag, perm)
-	if err != nil {
-		return nil, err
+	for {
+		fd, e := fsOpen(name, flag|modelOpenFlags, syscallMode(perm))
+		if e == 0 {
+			inner := &file{name: name}
+			inner.pfd.Sysfd = fd
+			inner.pfd.IsStream = true
+			inner.pfd.ZeroReadIsEOF = true
+			return &File{inner}, nil
+		}
+		if e != 4 { // EINTR
+			return nil, modelPathError("open", name, modelErrno(e))
+		}
 	}
-	f.appendMode = flag&O_APPEND != 0
-
-	return f, nil
 }
```

##### `File.Close`
```diff
--- go
+++ model
@@ -1,11 +1,33 @@
-// file_posix.go
-// Close closes the [File], rendering it unusable for I/O.
-// On files that support [File.SetDeadline], any pending I/O operations will
-// be canceled and return immediately with an [ErrClosed] error.
-// Close will return an error if it has already been called.
+// model.go
+// MODEL: (*File).Close (file_posix.go, file_unix.go's file.close): a nil *File returns ErrInvalid
+// without a system call (Go's own first line); a closed one (fd -1) returns
+// &PathError{"close", name, ErrClosed} without one (Go: pfd.Close's increfAndClose fails with
+// ErrFileClosing, which close maps to ErrClosed; examples/osfs/semantics/model_os_close_twice.go).
+// Otherwise close(2), not retried on EINTR (Linux frees the fd whatever the errno), and pfd.Sysfd
+// set to -1 (Go's pfd.destroy). The extension's Close frees the fd whatever its errno; DirClose for
+// a directory's fd, OutClose for a directory's outside the roots' trees (fsFdKind, a query of the
+// model's state, not a system call, decides).
 func (f *File) Close() error {
 	if f == nil {
 		return ErrInvalid
 	}
-	return f.file.close()
+	inner := f.file
+	fd := inner.pfd.Sysfd
+	if fd == -1 {
+		return modelPathError("close", inner.name, ErrClosed)
+	}
+	kind := fsFdKind(fd)
+	inner.pfd.Sysfd = -1
+	var e uintptr
+	if kind == 0 {
+		e = fsClose(fd)
+	} else if kind == 1 {
+		e = fsDirClose(fd)
+	} else {
+		e = fsOutClose(fd)
+	}
+	if e == 0 {
+		return nil
+	}
+	return modelWrapErrno("close", inner, e)
 }
```

##### `File.ReadAt`
```diff
--- go
+++ model
@@ -1,26 +1,37 @@
-// file.go
-// ReadAt reads len(b) bytes from the File starting at byte offset off.
-// It returns the number of bytes read and the error, if any.
-// ReadAt always returns a non-nil error when n < len(b).
-// At end of file, that error is io.EOF.
+// model.go
+// MODEL: (*File).ReadAt (file.go, poll.FD.Pread). A negative offset returns Go's error without a
+// system call. Otherwise Go's loop: pread(2) of at most modelMaxRW bytes, EINTR retried; an error
+// ends it with f.wrapErr("read", e); a read of 0 bytes ends it with io.EOF; a short read is
+// followed by another. fsPRead's data is copied into b (a failed pread may have written a prefix of
+// b, which is copied and not counted, as in Go).
 func (f *File) ReadAt(b []byte, off int64) (n int, err error) {
-	if err := f.checkValid("read"); err != nil {
-		return 0, err
+	inner := f.file
+	if off < 0 {
+		return 0, modelPathError("readat", inner.name, errors.New("negative offset"))
 	}
-
-	if off < 0 {
-		return 0, &PathError{Op: "readat", Path: f.name, Err: errors.New("negative offset")}
+	fd := inner.pfd.Sysfd
+	for {
+		l := len(b)
+		if l == 0 {
+			return n, nil
+		}
+		k := l
+		if k > modelMaxRW {
+			k = modelMaxRW
+		}
+		data, e := fsPRead(fd, off, k)
+		m := copy(b, data)
+		if e == 4 { // EINTR
+			continue
+		}
+		if e != 0 {
+			return n, modelWrapErrno("read", inner, e)
+		}
+		if m == 0 {
+			return n, io.EOF
+		}
+		b = b[m:l]
+		off += int64(m)
+		n += m
 	}
-
-	for len(b) > 0 {
-		m, e := f.pread(b, off)
-		if e != nil {
-			err = f.wrapErr("read", e)
-			break
-		}
-		n += m
-		b = b[m:]
-		off += int64(m)
-	}
-	return
 }
```

##### `File.WriteAt`
```diff
--- go
+++ model
@@ -1,30 +1,36 @@
-// file.go
-// WriteAt writes len(b) bytes to the File starting at byte offset off.
-// It returns the number of bytes written and an error, if any.
-// WriteAt returns a non-nil error when n != len(b).
-//
-// If file was opened with the [O_APPEND] flag, WriteAt returns an error.
+// model.go
+// MODEL: (*File).WriteAt (file.go, poll.FD.Pwrite). A negative offset returns Go's error without a
+// system call. Pwrite returns all of p written, or an error, so WriteAt's loop runs once: (len(b),
+// nil) or (0, f.wrapErr("write", e)). Pwrite's loop writes p[nn:max] (at most modelMaxRW bytes) at
+// off+nn, EINTR retried, until all is written or an error. Each pwrite(2) is fsPWrite (the
+// extension's PWriteStart and PWriteFinish), never of empty data; with errno 0 it always writes
+// something, so Pwrite's io.ErrUnexpectedEOF branch is unreachable.
 func (f *File) WriteAt(b []byte, off int64) (n int, err error) {
-	if err := f.checkValid("write"); err != nil {
-		return 0, err
+	inner := f.file
+	if off < 0 {
+		return 0, modelPathError("writeat", inner.name, errors.New("negative offset"))
 	}
-	if f.appendMode {
-		return 0, errWriteAtInAppendMode
+	fd := inner.pfd.Sysfd
+	l := len(b)
+	if l == 0 {
+		return 0, nil
 	}
-
-	if off < 0 {
-		return 0, &PathError{Op: "writeat", Path: f.name, Err: errors.New("negative offset")}
+	nn := 0
+	for {
+		max := l
+		if l-nn > modelMaxRW {
+			max = nn + modelMaxRW
+		}
+		w, e := fsPWrite(fd, off+int64(nn), string(b[nn:max]))
+		if e == 4 { // EINTR
+			continue
+		}
+		nn += w
+		if nn == l && e == 0 {
+			return l, nil
+		}
+		if e != 0 {
+			return 0, modelWrapErrno("write", inner, e)
+		}
 	}
-
-	for len(b) > 0 {
-		m, e := f.pwrite(b, off)
-		if e != nil {
-			err = f.wrapErr("write", e)
-			break
-		}
-		n += m
-		b = b[m:]
-		off += int64(m)
-	}
-	return
 }
```

##### `File.Seek`
```diff
--- go
+++ model
@@ -1,19 +1,55 @@
-// file.go
-// Seek sets the offset for the next Read or Write on file to offset, interpreted
-// according to whence: 0 means relative to the origin of the file, 1 means
-// relative to the current offset, and 2 means relative to the end.
-// It returns the new offset and an error, if any.
-// The behavior of Seek on a file opened with [O_APPEND] is not specified.
+// model.go
+// MODEL: (*File).Seek (file.go, file_unix.go's seek, poll.FD.Seek): one lseek(2). Linux computes
+// the new offset from 0 (SEEK_SET), the offset (SEEK_CUR) or the size (SEEK_END, the extension's
+// Fstat: the model has more errnos than lseek's, only more outcomes), and fails with EINVAL on
+// a whence above SEEK_HOLE or a negative result, changing nothing.
+// Past modelSeekMax (ext4's limit for a regular file) a regular file's lseek answers EINVAL.
+// Not modelled (gomodel.Stuck): a closed file, SEEK_DATA/SEEK_HOLE (3, 4: ext4 answers them),
+// SEEK_CUR from an unknown offset (also a directory's after Readdirnames: getdents moves its offset,
+// to 2^63-1 at the end of an ext4 htree directory), SEEK_END of a directory (ext4 answers from the
+// htree's end, 2^63-1, not from the size), a directory's result past modelSeekMax (its limit is
+// 2^63-1), a result at or past modelOffMax.
 func (f *File) Seek(offset int64, whence int) (ret int64, err error) {
-	if err := f.checkValid("seek"); err != nil {
-		return 0, err
+	inner := f.file
+	fd := inner.pfd.Sysfd
+	if fd < 0 {
+		gomodel.Stuck()
 	}
-	r, e := f.seek(offset, whence)
-	if e == nil && f.dirinfo.Load() != nil && r != 0 {
-		e = syscall.EISDIR
+	cur := inner.off
+	var base int64
+	var e uintptr
+	if whence == 0 {
+	} else if whence == 1 {
+		if cur < 0 {
+			gomodel.Stuck()
+		}
+		base = cur
+	} else if whence == 2 {
+		if fsFdKind(fd) != 0 {
+			gomodel.Stuck()
+		}
+		base, e = fsFstat(fd)
+	} else if whence == 3 || whence == 4 {
+		gomodel.Stuck()
+	} else {
+		e = 22 // EINVAL
 	}
-	if e != nil {
-		return 0, f.wrapErr("seek", e)
+	if e != 0 {
+		return 0, modelWrapErrno("seek", inner, e)
 	}
-	return r, nil
+	n := base + offset
+	if n < 0 {
+		return 0, modelWrapErrno("seek", inner, 22)
+	}
+	if modelOffMax <= n || modelOffMax <= base || modelOffMax <= offset {
+		gomodel.Stuck()
+	}
+	if modelSeekMax < n {
+		if fsFdKind(fd) == 0 {
+			return 0, modelWrapErrno("seek", inner, 22)
+		}
+		gomodel.Stuck()
+	}
+	inner.off = n
+	return n, nil
 }
```

##### `File.Write`
```diff
--- go
+++ model
@@ -1,24 +1,42 @@
-// file.go
-// Write writes len(b) bytes from b to the File.
-// It returns the number of bytes written and an error, if any.
-// Write returns a non-nil error when n != len(b).
+// model.go
+// MODEL: (*File).Write (file.go, file_posix.go's write, poll.FD.Write): write(2) calls at the file
+// offset until all of b is written, EINTR retried, the offset advancing by what was written. A
+// write(2) is a pwrite(2) at the offset that then moves it: the model calls WriteAt at off, then
+// moves off past b. On an error Go returns the bytes written before it, which WriteAt does not
+// keep: the model returns any count, and the offset is unknown (-1). An empty b, for which Go issues
+// a zero-byte write(2) whose answer depends on the fd's mode (EBADF on a read-only fd), returns
+// (0, nil) or (0, f.wrapErr("write", e)) for any errno, changing nothing (POSIX; measured,
+// TestEmptyWrite; examples/osfs/semantics/model_os_writefile.go). Not modelled: a closed file, an
+// unknown offset, a write reaching modelOffMax. Concurrent Write or Read calls on one File, which
+// Go serializes (poll.FD's fdMutex; Linux's f_pos update is atomic), read and write off without a
+// lock here: the model has at least Go's outcomes (also lost offset updates, which Go has not; in
+// gc builds os's TestWriteAtConcurrent fails for that reason).
 func (f *File) Write(b []byte) (n int, err error) {
-	if err := f.checkValid("write"); err != nil {
-		return 0, err
+	inner := f.file
+	fd := inner.pfd.Sysfd
+	off := inner.off
+	l := len(b)
+	if fd < 0 {
+		gomodel.Stuck()
 	}
-	n, e := f.write(b)
-	if n < 0 {
-		n = 0
+	if l == 0 {
+		e := uintptr(gomodel.ChooseUint64())
+		if e == 0 {
+			return 0, nil
+		}
+		return 0, modelWrapErrno("write", inner, e)
 	}
-	if n != len(b) {
-		err = io.ErrShortWrite
+	if off < 0 {
+		gomodel.Stuck()
 	}
-
-	epipecheck(f, e)
-
-	if e != nil {
-		err = f.wrapErr("write", e)
+	if modelOffMax <= off+int64(l) {
+		gomodel.Stuck()
 	}
-
-	return n, err
+	n, err = f.WriteAt(b, off)
+	if err == nil {
+		inner.off = off + int64(l)
+		return n, err
+	}
+	inner.off = -1
+	return int(gomodel.ChooseUint64()), err
 }
```

##### `File.Read`
```diff
--- go
+++ model
@@ -1,11 +1,44 @@
-// file.go
-// Read reads up to len(b) bytes from the File and stores them in b.
-// It returns the number of bytes read and any error encountered.
-// At end of file, Read returns 0, io.EOF.
+// model.go
+// MODEL: (*File).Read (file.go, file_posix.go's read, poll.FD.Read): for a non-empty b, one
+// read(2) at the file offset of at most modelMaxRW bytes, EINTR retried; the offset advances by
+// what was read; 0 bytes is io.EOF; an error is f.wrapErr("read", e) with n = 0, the offset
+// unchanged. A read(2) is a pread(2) at the offset that then moves it (fsPRead at off, its bytes
+// copied into b). An empty b returns 0, nil at once (poll.FD.Read). Not modelled: a closed file, an
+// unknown offset, a read reaching modelOffMax.
 func (f *File) Read(b []byte) (n int, err error) {
-	if err := f.checkValid("read"); err != nil {
-		return 0, err
+	inner := f.file
+	fd := inner.pfd.Sysfd
+	off := inner.off
+	l := len(b)
+	if fd < 0 {
+		gomodel.Stuck()
 	}
-	n, e := f.read(b)
-	return n, f.wrapErr("read", e)
+	if l == 0 {
+		return 0, nil
+	}
+	if off < 0 {
+		gomodel.Stuck()
+	}
+	if modelOffMax <= off+int64(l) {
+		gomodel.Stuck()
+	}
+	for {
+		k := l
+		if k > modelMaxRW {
+			k = modelMaxRW
+		}
+		data, e := fsPRead(fd, off, k)
+		if e == 4 { // EINTR
+			continue
+		}
+		if e != 0 {
+			return 0, modelWrapErrno("read", inner, e)
+		}
+		m := copy(b, data)
+		inner.off = off + int64(m)
+		if m == 0 {
+			return 0, io.EOF
+		}
+		return m, nil
+	}
 }
```

##### `File.Stat`
```diff
--- go
+++ model
@@ -1,15 +1,23 @@
-// stat_unix.go
-// Stat returns the [FileInfo] structure describing file.
-// If there is an error, it will be of type [*PathError].
+// model.go
+// MODEL: (*File).Stat (stat_unix.go): fstat(2), EINTR retried, into a fresh fileStat
+// (fillFileStatFromSys(&fs, f.name)), an error being f.wrapErr("stat", e) with a nil FileInfo. The
+// extension's Fstat gives only the size, and is stuck on a directory's fd, so the mode is a regular
+// file's (modelMode(0)); the name is filepathlite.Base(f.name), as fillFileStatFromSys sets it.
 func (f *File) Stat() (FileInfo, error) {
-	if f == nil {
-		return nil, ErrInvalid
+	inner := f.file
+	fd := inner.pfd.Sysfd
+	for {
+		size, e := fsFstat(fd)
+		if e == 4 { // EINTR
+			continue
+		}
+		if e != 0 {
+			return nil, modelWrapErrno("stat", inner, e)
+		}
+		fs := &fileStat{}
+		fs.name = filepathlite.Base(inner.name)
+		fs.size = size
+		fs.mode = modelMode(0)
+		return fs, nil
 	}
-	var fs fileStat
-	err := f.pfd.Fstat(&fs.sys)
-	if err != nil {
-		return nil, f.wrapErr("stat", err)
-	}
-	fillFileStatFromSys(&fs, f.name)
-	return &fs, nil
 }
```

##### `File.Truncate`
```diff
--- go
+++ model
@@ -1,13 +1,25 @@
-// file_posix.go
-// Truncate changes the size of the file.
-// It does not change the I/O offset.
-// If there is an error, it will be of type [*PathError].
+// model.go
+// MODEL: (*File).Truncate (file_posix.go, poll.FD.Ftruncate): ftruncate(2), EINTR retried, an
+// error being f.wrapErr("truncate", e). A negative size is EINVAL, which Linux answers before
+// looking at the fd, without a system call (the extension's ftruncate is stuck on it). fsFtruncate
+// is the extension's FtruncateStart and FtruncateFinish. Not modelled: a closed file.
 func (f *File) Truncate(size int64) error {
-	if err := f.checkValid("truncate"); err != nil {
-		return err
+	inner := f.file
+	fd := inner.pfd.Sysfd
+	if fd < 0 {
+		gomodel.Stuck()
 	}
-	if e := f.pfd.Ftruncate(size); e != nil {
-		return f.wrapErr("truncate", e)
+	if size < 0 {
+		return modelWrapErrno("truncate", inner, 22)
 	}
-	return nil
+	for {
+		e := fsFtruncate(fd, size)
+		if e == 4 { // EINTR
+			continue
+		}
+		if e != 0 {
+			return modelWrapErrno("truncate", inner, e)
+		}
+		return nil
+	}
 }
```

##### `File.Sync`
```diff
--- go
+++ model
@@ -1,13 +1,27 @@
-// file_posix.go
-// Sync commits the current contents of the file to stable storage.
-// Typically, this means flushing the file system's in-memory copy
-// of recently written data to disk.
+// model.go
+// MODEL: (*File).Sync (file_posix.go, poll.FD.Fsync): fsync(2), EINTR retried, an error being
+// f.wrapErr("sync", e): the extension's Fsync, DirSync for a directory's fd, OutSync for a
+// directory's outside the roots' trees (fsFdKind). A failed Fsync changes nothing (the extension
+// assumes no failed writeback) and never returns EINTR.
 func (f *File) Sync() error {
-	if err := f.checkValid("sync"); err != nil {
-		return err
+	inner := f.file
+	fd := inner.pfd.Sysfd
+	kind := fsFdKind(fd)
+	for {
+		var e uintptr
+		if kind == 0 {
+			e = fsFsync(fd)
+		} else if kind == 1 {
+			e = fsDirSync(fd)
+		} else {
+			e = fsOutSync(fd)
+		}
+		if e == 4 { // EINTR
+			continue
+		}
+		if e != 0 {
+			return modelWrapErrno("sync", inner, e)
+		}
+		return nil
 	}
-	if e := f.pfd.Fsync(); e != nil {
-		return f.wrapErr("sync", e)
-	}
-	return nil
 }
```

##### `Rename`
```diff
--- go
+++ model
@@ -1,10 +1,24 @@
-// file.go
-// Rename renames (moves) oldpath to newpath.
-// If newpath already exists and is not a directory, Rename replaces it.
-// If newpath already exists and is a directory, Rename returns an error.
-// OS-specific restrictions may apply when oldpath and newpath are in different directories.
-// Even within the same directory, on non-Unix platforms Rename is not an atomic operation.
-// If there is an error, it will be of type *LinkError.
+// model.go
+// MODEL: Rename (file.go, file_unix.go's rename). Go first Lstat's newname; for a directory it
+// returns a LinkError: EEXIST, or the error of the Lstat of oldname (two distinct names of the
+// namespace are never the same file: no hard links, a case-sensitive filesystem, so SameFile is
+// false). fsLstatDir answers that question (isDir 1 only for a directory, with the errno to return;
+// 0 otherwise, and for a directory whose lstat failed, as in Go). Then rename(2), EINTR retried
+// (the extension's Rename, after its own CallBegin, each attempt). Go's body is not translated: its
+// SameFile reads fileStat.sys, which the models leave zero.
 func Rename(oldpath, newpath string) error {
-	return rename(oldpath, newpath)
+	isDir, le := fsLstatDir(newpath)
+	if isDir == 1 {
+		return &LinkError{"rename", oldpath, newpath, modelErrno(le)}
+	}
+	for {
+		e := fsRename(oldpath, newpath)
+		if e == 4 { // EINTR
+			continue
+		}
+		if e != 0 {
+			return &LinkError{"rename", oldpath, newpath, modelErrno(e)}
+		}
+		return nil
+	}
 }
```

##### `File.Readdirnames`
```diff
--- go
+++ model
@@ -1,29 +1,44 @@
-// dir.go
-// Readdirnames reads the contents of the directory associated with file
-// and returns a slice of up to n names of files in the directory,
-// in directory order. Subsequent calls on the same file will yield
-// further names.
-//
-// If n > 0, Readdirnames returns at most n names. In this case, if
-// Readdirnames returns an empty slice, it will return a non-nil error
-// explaining why. At the end of a directory, the error is [io.EOF].
-//
-// If n <= 0, Readdirnames returns all the names from the directory in
-// a single slice. In this case, if Readdirnames succeeds (reads all
-// the way to the end of the directory), it returns the slice and a
-// nil error. If it encounters an error before the end of the
-// directory, Readdirnames returns the names read until that point and
-// a non-nil error.
+// model.go
+// MODEL: (*File).Readdirnames (dir.go, dir_unix.go's readdir) for n <= 0: every name of the
+// directory but . and .., read by getdents(2) calls until one returns nothing (EINTR retried); an
+// error returns the names so far and &PathError{"readdirent", name, Errno(e)}; the result is never a
+// nil slice. The extension's DirReadNext gives a name at a time, with POSIX's readdir across
+// concurrent changes; it is stuck on a fd that is not a directory's (Go: ENOTDIR) and on a second
+// read of one fd (Go returns no names). n > 0 is not modelled, nor a directory whose offset is not 0
+// (Go's getdents reads from the offset a Seek set). getdents(2) moves the offset (f_pos: on ext4 a
+// hash cookie, 2^63-1 at the end), so the model makes it unknown (-1: a later Seek SEEK_CUR is
+// stuck). Before each append the loop assumes
+// (an infinite loop otherwise, Perennial's assume) that fewer than 2^44 names were read: Go's append
+// panics ("growslice: len out of range") once a []string's capacity passes maxAlloc/16 = 2^44
+// (linux/amd64), so the assumption excludes only executions Go ends in that runtime panic, which
+// Perennial's append treats as an assumption already
+// (examples/osfs/semantics/model_os_readdirnames_len.go).
 func (f *File) Readdirnames(n int) (names []string, err error) {
-	if f == nil {
-		return nil, ErrInvalid
+	inner := f.file
+	fd := inner.pfd.Sysfd
+	if n > 0 {
+		gomodel.Stuck()
 	}
-	names, _, _, err = f.readdir(n, readdirName)
-	if names == nil {
-		// Readdirnames has historically always returned a non-nil empty slice, never nil,
-		// even on error (except misuse with nil receiver above).
-		// Keep it that way to avoid breaking overly sensitive callers.
-		names = []string{}
+	if inner.off != 0 {
+		gomodel.Stuck()
 	}
-	return names, err
+	inner.off = -1
+	names = []string{}
+	for {
+		nm, done, e := fsDirReadNext(fd)
+		if e == 4 { // EINTR
+			continue
+		}
+		if e != 0 {
+			return names, modelWrapErrno("readdirent", inner, e)
+		}
+		if done == 1 {
+			return names, nil
+		}
+		if len(names) >= 1<<44 {
+			for {
+			}
+		}
+		names = append(names, nm)
+	}
 }
```

##### `Stat`
```diff
--- go
+++ model
@@ -1,7 +1,6 @@
-// stat.go
-// Stat returns a [FileInfo] describing the named file.
-// If there is an error, it will be of type [*PathError].
+// model.go
+// MODEL: Stat (stat.go): testlog.Stat(name), a no-op outside go test's logging (its logger is
+// nil), then statNolog: modelStat with Op "stat".
 func Stat(name string) (FileInfo, error) {
-	testlog.Stat(name)
-	return statNolog(name)
+	return modelStat("stat", name)
 }
```

##### `Lstat`
```diff
--- go
+++ model
@@ -1,13 +1,7 @@
-// stat.go
-// Lstat returns a [FileInfo] describing the named file.
-// If the file is a symbolic link, the returned FileInfo
-// describes the symbolic link. Lstat makes no attempt to follow the link.
-// If there is an error, it will be of type [*PathError].
-//
-// On Windows, if the file is a reparse point that is a surrogate for another
-// named entity (such as a symbolic link or mounted folder), the returned
-// FileInfo describes the reparse point, and makes no attempt to resolve it.
+// model.go
+// MODEL: Lstat (stat.go): testlog.Stat(name), then lstatNolog: modelStat with Op "lstat". In the
+// roots' trees there are no symlinks and no root is one (the extension's environment), so lstat
+// answers as stat does on every path below an ancestor of a root.
 func Lstat(name string) (FileInfo, error) {
-	testlog.Stat(name)
-	return lstatNolog(name)
+	return modelStat("lstat", name)
 }
```

##### `RemoveAll`
```diff
--- go
+++ model
@@ -1,9 +1,70 @@
-// path.go
-// RemoveAll removes path and any children it contains.
-// It removes everything it can but returns the first error
-// it encounters. If the path does not exist, RemoveAll
-// returns nil (no error).
-// If there is an error, it will be of type [*PathError].
+// model.go
+// MODEL: RemoveAll (path.go, removeall_at.go). Go's body:
+//
+//	if path == "" { return nil }
+//	if endsWithDot(path) { return &PathError{"RemoveAll", path, EINVAL} }
+//	err := Remove(path)
+//	if err == nil || IsNotExist(err) { return nil }
+//	parentDir, base := splitPath(path)
+//	parent, err := OpenFile(parentDir, O_RDONLY, 0)
+//	if IsNotExist(err) { return nil }
+//	if err != nil { return err }
+//	defer parent.Close()
+//	if err := removeAllFrom(parent.Fd(), base); err != nil {
+//		if pathErr, ok := err.(*PathError); ok { pathErr.Path = parentDir + "/" + pathErr.Path }
+//		return err
+//	}
+//	return nil
+//
+// Below Remove it is over the *at system calls (unlinkat, openat relative to a directory's fd),
+// which the extension does not have (its steps name paths). The model is that body over paths:
+// Remove inlined (for its errno), the parent opened as OpenFile does (and closed), and removeAllFrom
+// with each entry named by its path (modelRemoveAllFrom). A path and a name under an open
+// directory's fd name the same entry as long as no directory above it is moved: the model holds a
+// CallBegin of path from its start to its return (fsWithCall), so that every rename of a directory
+// in path's root's tree by another thread is stuck while it runs (the extension's Rename), and the
+// proved programs, which are never stuck, have no such rename. What is left is a directory above it
+// removed and another made in its place by another thread (Go's *at calls then act on the removed
+// one, which no path names, and fail or change nothing a path can see; the model's calls on the new
+// one may fail with any errno and no effect, the outcome Linux's leave visible). path must be
+// strictly below a root and canonical: the model is stuck on any other (as every path step).
+// examples/osfs/semantics/model_os_removeall.go.
 func RemoveAll(path string) error {
-	return removeAll(path)
+	if path == "" {
+		return nil
+	}
+	if endsWithDot(path) {
+		return modelPathError("RemoveAll", path, modelErrno(22))
+	}
+	return fsWithCall(path, func() error {
+		e := modelUnlinkLoop(path)
+		if e == 0 {
+			return nil
+		}
+		e1 := modelRmdirLoop(path)
+		if e1 == 0 {
+			return nil
+		}
+		if e1 != 20 { // ENOTDIR: Remove keeps unlink's errno
+			e = e1
+		}
+		if e == 2 {
+			return nil
+		}
+		parentDir, base := splitPath(path)
+		fd, oe := modelOpenLoop(parentDir)
+		if oe == 2 {
+			return nil
+		}
+		if oe != 0 {
+			return modelPathError("open", parentDir, modelErrno(oe))
+		}
+		pe := modelRemoveAllFrom(parentDir, base)
+		modelCloseFd(fd)
+		if pe == nil {
+			return nil
+		}
+		modelPrefixPath(pe, parentDir)
+		return pe
+	})
 }
```

##### `File.copyFileRange`
```diff
--- go
+++ model
@@ -1,3 +1,7 @@
-// zero_copy_linux.go
+// model.go
+// MODEL: (*File).copyFileRange (zero_copy_linux.go): Go's body, with
+// pollCopyFileRange(&f.pfd, &src.pfd, remain) as modelPollCopyFileRange of the two files (it needs
+// their kernel offsets, which poll.FD does not hold). Go reads the function from the package
+// variable pollCopyFileRange, which only os's tests reassign.
 func (f *File) copyFileRange(r io.Reader) (written int64, handled bool, err error) {
 	var (
@@ -20,10 +24,8 @@
 
 	if src.checkValid("ReadFrom") != nil {
-		// Avoid returning the error as we report handled as false,
-		// leave further error handling as the responsibility of the caller.
 		return 0, false, nil
 	}
 
-	written, handled, err = pollCopyFileRange(&f.pfd, &src.pfd, remain)
+	written, handled, err = modelPollCopyFileRange(f.file, src.file, remain)
 	if lr != nil {
 		lr.N -= written
```

Model-only declarations (additions, stubs; no real counterpart is replaced): `fsClose`, `fsDirClose`, `fsDirReadNext`, `fsDirSync`, `fsFdKind`, `fsFstat`, `fsFsync`, `fsFtruncate`, `fsLstatDir`, `fsOpen`, `fsOutClose`, `fsOutSync`, `fsPRead`, `fsPWrite`, `fsPathKind`, `fsRename`, `fsRmdir`, `fsUnlink`, `fsWithCall`, `modelCloseFd`, `modelCopyFileRangeRound`, `modelDirNames`, `modelDirNamesMu`, `modelErrno`, `modelGcErrno`, `modelHandleCopyFileRangeErr`, `modelMode`, `modelOpenLoop`, `modelPathError`, `modelPathErrorPtr`, `modelPollCopyFileRange`, `modelPrefixPath`, `modelRemoveAllFrom`, `modelRmdirLoop`, `modelStat`, `modelStatAbove`, `modelUnlinkLoop`, `modelWrapErrno`



## syscall (etcd-grove)

#### `Code/syscall.toml` — model `models/syscall`, 9 replaced declarations

##### `errnoErr`
```diff
--- go
+++ model
@@ -1,15 +1,11 @@
-// syscall_unix.go
-// errnoErr returns common boxed Errno values, to prevent
-// allocations at runtime.
+// model.go
+// MODEL: errnoErr (syscall_unix.go): nil for 0, else e as an error. Go returns the preallocated
+// errEAGAIN, errEINVAL or errENOENT for those three errnos (to avoid an allocation); each holds the
+// boxed Errno of the same value, so the two are equal interface values and no Go code can tell them
+// apart (reflection and unsafe are not modelled). (The preallocated variables are translated; the
+// model only spares the proofs Go's switch.)
 func errnoErr(e Errno) error {
-	switch e {
-	case 0:
+	if e == 0 {
 		return nil
-	case EAGAIN:
-		return errEAGAIN
-	case EINVAL:
-		return errEINVAL
-	case ENOENT:
-		return errENOENT
 	}
 	return e
```

##### `init.0`
```diff
--- go
+++ model
@@ -1,33 +1,13 @@
-// rlimit.go
-// Some systems set an artificially low soft limit on open file count, for compatibility
-// with code that uses select and its hard-coded maximum file descriptor
-// (limited by the size of fd_set).
+// model.go
+// MODEL: syscall's init function (rlimit.go) raises the process's soft limit on open files through
+// the raw prlimit system call (RawSyscall6, assembly) and records the original limit in
+// origRlimitNofile, which only Setrlimit and exec read. It cannot panic. The model does nothing: the
+// changed limit and origRlimitNofile are observable only through exec, a Getrlimit system call
+// (neither modelled) or running out of file descriptors, and the file extension's Open may fail with
+// any errno, EMFILE included, whatever the limit. (Running out can also end the process, when the
+// netpoller's epoll_create1 fails: a prefix of a model run, which a partial-correctness triple does
+// not contradict.) The user's decision, Perennial fix-semantics Case 33, 2026-11-04.
 //
-// Go does not use select, so it should not be subject to these limits.
-// On some systems the limit is 256, which is very easy to run into,
-// even in simple programs like gofmt when they parallelize walking
-// a file tree.
-//
-// After a long discussion on go.dev/issue/46279, we decided the
-// best approach was for Go to raise the limit unconditionally for itself,
-// and then leave old software to set the limit back as needed.
-// Code that really wants Go to leave the limit alone can set the hard limit,
-// which Go of course has no choice but to respect.
+//gomodel:replace init.0 "var lim Rlimit"
 func init() {
-	var lim Rlimit
-	if err := Getrlimit(RLIMIT_NOFILE, &lim); err == nil && lim.Max > 0 && lim.Cur < lim.Max-1 {
-		origRlimitNofile.Store(&lim)
-		nlim := lim
-
-		// We set Cur to Max - 1 so that we are more likely to
-		// detect cases where another process uses prlimit
-		// to change our resource limits. The theory is that
-		// using prlimit to change to Cur == Max is more likely
-		// than using prlimit to change to Cur == Max - 1.
-		// The place we check for this is in exec_linux.go.
-		nlim.Cur = nlim.Max - 1
-
-		adjustFileLimit(&nlim)
-		setrlimit(RLIMIT_NOFILE, &nlim)
-	}
 }
```

##### `Fdatasync`
```diff
--- go
+++ model
@@ -1,8 +1,7 @@
-// zsyscall_linux_amd64.go
+// model.go
+// MODEL: Fdatasync (zsyscall_linux_amd64.go): fdatasync(2), which the extension does not tell
+// apart from fsync(2) (Linux's fdatasync also flushes the size, all the metadata the extension has):
+// its Fsync (stuck on an fd that is not open, else success or any nonzero errno).
 func Fdatasync(fd int) (err error) {
-	_, _, e1 := Syscall(SYS_FDATASYNC, uintptr(fd), 0, 0)
-	if e1 != 0 {
-		err = errnoErr(e1)
-	}
-	return
+	return errnoErr(Errno(fsFsync(fd)))
 }
```

##### `Flock`
```diff
--- go
+++ model
@@ -1,8 +1,10 @@
-// zsyscall_linux_amd64.go
+// model.go
+// MODEL: Flock (zsyscall_linux_amd64.go): flock(2), one Syscall, EINTR not retried: the
+// extension's Flock, the lock rule on the description's flock lock (a lock succeeds only when no
+// other open file description of the file holds a conflicting one, two opens in one process
+// conflicting; a blocking one waits; any request may fail with any errno and no change, EWOULDBLOCK
+// included). Stuck on an fd that is not a file's, on another how, and on re-locking a description.
+// examples/osfs/semantics/locks_flock.go, locks_blocking.go, locks_spurious_eagain.go.
 func Flock(fd int, how int) (err error) {
-	_, _, e1 := Syscall(SYS_FLOCK, uintptr(fd), uintptr(how), 0)
-	if e1 != 0 {
-		err = errnoErr(e1)
-	}
-	return
+	return errnoErr(Errno(fsFlock(fd, how)))
 }
```

##### `Fallocate`
```diff
--- go
+++ model
@@ -1,8 +1,17 @@
-// zsyscall_linux_amd64.go
+// model.go
+// MODEL: Fallocate (zsyscall_linux_amd64.go): one fallocate(2), EINTR not retried. Mode 0 is the
+// extension's FallocStart, a resize to max(size, off + len) in flight, and FallocFinish (on failure
+// any size between); FALLOC_FL_KEEP_SIZE (1) is FallocKeep, no visible change, any errno. Both are
+// stuck on a negative off or a len not above 0 (Linux: EINVAL, misuse) and on an fd that is not a
+// writable file's. Other modes (punching, zeroing, collapsing, inserting) are not modelled.
+// examples/osfs/semantics/model_syscall_fallocate.go.
 func Fallocate(fd int, mode uint32, off int64, len int64) (err error) {
-	_, _, e1 := Syscall6(SYS_FALLOCATE, uintptr(fd), uintptr(mode), uintptr(off), uintptr(len), 0, 0)
-	if e1 != 0 {
-		err = errnoErr(e1)
+	if mode == 0 {
+		return errnoErr(Errno(fsFalloc(fd, off, len)))
 	}
-	return
+	if mode == 1 {
+		return errnoErr(Errno(fsFallocKeep(fd, off, len)))
+	}
+	gomodel.Stuck()
+	return nil
 }
```

##### `FcntlFlock`
```diff
--- go
+++ model
@@ -1,9 +1,69 @@
-// flock_linux.go
-// FcntlFlock performs a fcntl syscall for the [F_GETLK], [F_SETLK] or [F_SETLKW] command.
+// model.go
+// MODEL: FcntlFlock (flock_linux.go): one fcntl(2) with the lock description lk
+// (fcntl64Syscall is SYS_FCNTL on amd64), nil for errno 0, else the Errno.
+//
+// F_OFD_SETLK (37) and F_OFD_SETLKW (38): Linux copies the description in (do_fcntl), so the model
+// loads Type, Whence, Start, Len, Pid (a concurrent write is a race a proof must exclude; the padding,
+// which no outcome depends on, is not loaded). A whole-file request (Whence SEEK_SET, Start and Len
+// 0) with Pid 0 and Type F_RDLCK (0), F_WRLCK (1) or F_UNLCK (2) is the extension's OfdLock of (fd,
+// (cmd, Type)): the lock rule on the description's OFD lock (as Flock's), any request failing with
+// any errno and no change. Anything else is not modelled: a byte range (Linux accepts it), Pid not 0
+// or another Type (Linux: EINVAL). Nothing is written back (F_SETLK copies nothing out).
+// examples/osfs/semantics/locks_ofd.go, locks_blocking.go.
+//
+// F_SETLK (6) and F_SETLKW (7), the per-process POSIX locks, are not modelled: they never conflict
+// within one process and closing any fd of the file releases them (locks_posix_not_modelled.go).
+//
+// F_OFD_GETLK (36), the query fileutil's initializer makes on fd 0 (lock_linux.go's init), on any fd,
+// one the process opened or not: no extension step (a query changes no state the model has), and
+// nil or any nonzero errno. Linux copies the whole struct in, and on success copies the whole struct
+// back: the lock description and the padding as read. So the model loads all seven fields at entry
+// and, on success, stores all seven: arbitrary values in Type, Whence, Start, Len and Pid, the
+// padding as loaded (measured, TestOFDGetlkPadding); a concurrent access is then a race, which a
+// proof must exclude. On failure lk is unchanged. A nil lk is stuck (Linux: EFAULT). Any other
+// command is not modelled. examples/osfs/semantics/model_syscall_fcntlflock.go.
 func FcntlFlock(fd uintptr, cmd int, lk *Flock_t) error {
-	_, _, errno := Syscall(fcntl64Syscall, fd, uintptr(cmd), uintptr(unsafe.Pointer(lk)))
-	if errno == 0 {
-		return nil
+	if cmd == 37 || cmd == 38 {
+		ty := lk.Type
+		wh := lk.Whence
+		st := lk.Start
+		ln := lk.Len
+		pid := lk.Pid
+		if wh == 0 && st == 0 && ln == 0 && pid == 0 {
+			if ty == 1 {
+				return errnoErr(Errno(fsOfdLock(fd, cmd, 1)))
+			}
+			if ty == 0 {
+				return errnoErr(Errno(fsOfdLock(fd, cmd, 0)))
+			}
+			if ty == 2 {
+				return errnoErr(Errno(fsOfdLock(fd, cmd, 2)))
+			}
+			gomodel.Stuck()
+		}
+		gomodel.Stuck()
 	}
-	return errno
+	if cmd == 36 {
+		_ = lk.Type
+		_ = lk.Whence
+		p0 := lk.Pad_cgo_0
+		_ = lk.Start
+		_ = lk.Len
+		_ = lk.Pid
+		p1 := lk.Pad_cgo_1
+		e := Errno(gomodel.ChooseUint64())
+		if e == 0 {
+			lk.Type = int16(gomodel.ChooseUint64())
+			lk.Whence = int16(gomodel.ChooseUint64())
+			lk.Pad_cgo_0 = p0
+			lk.Start = int64(gomodel.ChooseUint64())
+			lk.Len = int64(gomodel.ChooseUint64())
+			lk.Pid = int32(gomodel.ChooseUint64())
+			lk.Pad_cgo_1 = p1
+			return nil
+		}
+		return errnoErr(e)
+	}
+	gomodel.Stuck()
+	return nil
 }
```

##### `Mkdir`
```diff
--- go
+++ model
@@ -1,4 +1,20 @@
-// syscall_linux.go
+// model.go
+// MODEL: Mkdir (syscall_linux.go: Mkdirat(AT_FDCWD, path, mode), one mkdirat(2), EINTR not
+// retried here: os's ignoringEINTR retries): the extension's Mkdir of path, after its own CallBegin
+// (fsMkdir). At a root or a strict ancestor of one (fsPathKind 0 or 2), where the extension gives a
+// path no meaning, with no extension step: any nonzero errno (EEXIST on Linux). The environment keeps
+// the roots and their ancestors existing directories (a symlink to one, for an ancestor) that no step
+// of the program can remove or rename, so mkdir(2) of one fails (EEXIST, or any other errno), changing
+// nothing. (Until 2026-11-24 this was os.MkdirAll's mkdirAllAbove; os.MkdirAll is now Go's, over
+// this.) The mode matters only to a created directory's, which the extension does not model.
+// examples/osfs/semantics/model_os_mkdirall.go, model_os_mkdirall_above.go.
 func Mkdir(path string, mode uint32) (err error) {
-	return Mkdirat(_AT_FDCWD, path, mode)
+	if fsPathKind(path) != 1 {
+		e := Errno(gomodel.ChooseUint64())
+		if e == 0 {
+			e = EEXIST
+		}
+		return e
+	}
+	return errnoErr(Errno(fsMkdir(path, mode)))
 }
```

##### `Unlink`
```diff
--- go
+++ model
@@ -1,4 +1,6 @@
-// syscall_linux.go
+// model.go
+// MODEL: Unlink (syscall_linux.go: unlinkat(AT_FDCWD, path, 0), one unlinkat(2), EINTR not
+// retried here): the extension's Unlink of path, after its own CallBegin (fsUnlink).
 func Unlink(path string) error {
-	return unlinkat(_AT_FDCWD, path, 0)
+	return errnoErr(Errno(fsUnlink(path)))
 }
```

##### `Rmdir`
```diff
--- go
+++ model
@@ -1,4 +1,6 @@
-// syscall_linux.go
+// model.go
+// MODEL: Rmdir (syscall_linux.go: unlinkat(AT_FDCWD, path, AT_REMOVEDIR), one unlinkat(2), EINTR
+// not retried here): the extension's Rmdir of path, after its own CallBegin (fsRmdir).
 func Rmdir(path string) error {
-	return unlinkat(_AT_FDCWD, path, _AT_REMOVEDIR)
+	return errnoErr(Errno(fsRmdir(path)))
 }
```

Model-only declarations (additions, stubs; no real counterpart is replaced): `fsFalloc`, `fsFallocKeep`, `fsFlock`, `fsFsync`, `fsMkdir`, `fsOfdLock`, `fsPathKind`, `fsRmdir`, `fsUnlink`, `init`, `modelGcErrno`



## durable (etcd-grove)

#### `Code/github_com/mit_pdos/etcd_grove/examples/lib/durable.toml` — model `models/github.com/mit-pdos/etcd-grove/examples/lib/durable`, 2 replaced declarations

##### `Read`
```diff
--- go
+++ model
@@ -1,13 +1,11 @@
-// durable.go
-// Read returns the entire contents of the file name and true, or "" and false if there is no
-// such file.
+// model.go
+// MODEL: Read (durable.go): the durable-state extension's Read, one atomic step that cannot fail:
+// the entire contents of the file and true, or "" and false if there is none. What is trusted is that
+// Go's body (mu held; tryRead retried until it is done: os.Open, Stat, ReadAt, a missing file
+// fs.ErrNotExist) composes the operating system's file API into that operation; the model departs
+// from Go only by being less defined where Go keeps retrying forever (a persistent I/O error), as a
+// safety model need only cover the executions in which Go's returns. GooseLang/Ext/Durable/Impl.lean
+// lists the other divergences from a real filesystem.
 func Read(name string) (string, bool) {
-	mu.Lock()
-	defer mu.Unlock()
-	for {
-		s, ok, done := tryRead(name)
-		if done {
-			return s, ok
-		}
-	}
+	return durableRead(name)
 }
```

##### `Write`
```diff
--- go
+++ model
@@ -1,9 +1,9 @@
-// durable.go
-// Write replaces the entire contents of the file name by data, creating it if needed,
-// atomically and durably.
+// model.go
+// MODEL: Write (durable.go): the durable-state extension's Write, one atomic step that cannot fail,
+// after which the file holds data durably. Go's body (mu held; tryWrite retried until it succeeds: a
+// temporary file written, synced, renamed over the file and the directory synced) provides it with
+// the operating system's file API; the temporary files a Write interrupted by a crash leaves behind
+// are not in the model.
 func Write(name string, data string) {
-	mu.Lock()
-	defer mu.Unlock()
-	for !tryWrite(name, data) {
-	}
+	durableWrite(name, data)
 }
```

Model-only declarations (additions, stubs; no real counterpart is replaced): `durableRead`, `durableWrite`



## hash/crc32 (etcd-grove)

#### `Code/hash/crc32.toml` — model `models/hash/crc32`, 3 replaced declarations

##### `archAvailableCastagnoli`
```diff
--- go
+++ model
@@ -1,4 +1,10 @@
-// crc32_amd64.go
+// model.go
+// MODEL: archAvailableCastagnoli is `return cpu.X86.HasSSE42` in Go, a property of the CPU that
+// the runtime's cpuid assembly (internal/cpu's doinit, run by the runtime, not by package
+// initialization) sets: no translated code determines it. The model answers gomodel.Choose(), any
+// boolean at each call, so it covers every CPU (with or without SSE4.2, and the other
+// architectures' crc32_otherarch.go, whose answer is false). Only castagnoliInitOnce calls it, once
+// per process, so a per-call choice adds no behaviour Go lacks beyond a different CPU's.
 func archAvailableCastagnoli() bool {
-	return cpu.X86.HasSSE42
+	return gomodel.Choose()
 }
```

##### `archInitCastagnoli`
```diff
--- go
+++ model
@@ -1,22 +1,8 @@
-// crc32_amd64.go
-func archInitCastagnoli() {
-	if !cpu.X86.HasSSE42 {
-		panic("arch-specific Castagnoli not available")
-	}
-	castagnoliSSE42TableK1 = new(sse42Table)
-	castagnoliSSE42TableK2 = new(sse42Table)
-	// See description in updateCastagnoli.
-	//    t[0][i] = CRC(i000, O)
-	//    t[1][i] = CRC(0i00, O)
-	//    t[2][i] = CRC(00i0, O)
-	//    t[3][i] = CRC(000i, O)
-	// where O is a sequence of K zeros.
-	var tmp [castagnoliK2]byte
-	for b := 0; b < 4; b++ {
-		for i := 0; i < 256; i++ {
-			val := uint32(i) << uint32(b*8)
-			castagnoliSSE42TableK1[b][i] = castagnoliSSE42(val, tmp[:castagnoliK1])
-			castagnoliSSE42TableK2[b][i] = castagnoliSSE42(val, tmp[:])
-		}
-	}
-}
+// model.go
+// MODEL: archInitCastagnoli is a no-op. Go's panics unless cpu.X86.HasSSE42, which the package's
+// own code rules out (it calls this only after archAvailableCastagnoli() returned true), and
+// otherwise fills castagnoliSSE42TableK1/K2 by calls of the SSE4.2 assembly castagnoliSSE42 on a
+// zeroed stack buffer; only Go's archUpdateCastagnoli reads those two package variables. The
+// model's archUpdateCastagnoli reads neither, so leaving them nil changes no result, and Go's
+// version returns (it has no other effect and no failure).
+func archInitCastagnoli() {}
```

##### `archUpdateCastagnoli`
```diff
--- go
+++ model
@@ -1,111 +1,12 @@
-// crc32_amd64.go
+// model.go
+// MODEL: archUpdateCastagnoli returns the CRC-32C of crc and p as Go's portable code computes it
+// (simpleUpdate over simpleMakeTable(Castagnoli), crc32_generic.go). Go's computes it with SSE4.2
+// CRC32 instructions in three streams combined through the K1/K2 tables (crc32_amd64.s); it panics
+// unless cpu.X86.HasSSE42, which the package's code rules out (updateCastagnoli is set to it only
+// after archAvailableCastagnoli() returned true). Both read p and write nothing the caller sees
+// (the model's table is a fresh allocation). The trusted claim is that the assembly computes this
+// function: Go's own TestArchCastagnoli (crc32_test.go) compares archUpdateCastagnoli with
+// simpleUpdate over simpleMakeTable(Castagnoli) on every length up to and beyond its cutoffs.
 func archUpdateCastagnoli(crc uint32, p []byte) uint32 {
-	if !cpu.X86.HasSSE42 {
-		panic("not available")
-	}
-
-	// This method is inspired from the algorithm in Intel's white paper:
-	//    "Fast CRC Computation for iSCSI Polynomial Using CRC32 Instruction"
-	// The same strategy of splitting the buffer in three is used but the
-	// combining calculation is different; the complete derivation is explained
-	// below.
-	//
-	// -- The basic idea --
-	//
-	// The CRC32 instruction (available in SSE4.2) can process 8 bytes at a
-	// time. In recent Intel architectures the instruction takes 3 cycles;
-	// however the processor can pipeline up to three instructions if they
-	// don't depend on each other.
-	//
-	// Roughly this means that we can process three buffers in about the same
-	// time we can process one buffer.
-	//
-	// The idea is then to split the buffer in three, CRC the three pieces
-	// separately and then combine the results.
-	//
-	// Combining the results requires precomputed tables, so we must choose a
-	// fixed buffer length to optimize. The longer the length, the faster; but
-	// only buffers longer than this length will use the optimization. We choose
-	// two cutoffs and compute tables for both:
-	//  - one around 512: 168*3=504
-	//  - one around 4KB: 1344*3=4032
-	//
-	// -- The nitty gritty --
-	//
-	// Let CRC(I, X) be the non-inverted CRC32-C of the sequence X (with
-	// initial non-inverted CRC I). This function has the following properties:
-	//   (a) CRC(I, AB) = CRC(CRC(I, A), B)
-	//   (b) CRC(I, A xor B) = CRC(I, A) xor CRC(0, B)
-	//
-	// Say we want to compute CRC(I, ABC) where A, B, C are three sequences of
-	// K bytes each, where K is a fixed constant. Let O be the sequence of K zero
-	// bytes.
-	//
-	// CRC(I, ABC) = CRC(I, ABO xor C)
-	//             = CRC(I, ABO) xor CRC(0, C)
-	//             = CRC(CRC(I, AB), O) xor CRC(0, C)
-	//             = CRC(CRC(I, AO xor B), O) xor CRC(0, C)
-	//             = CRC(CRC(I, AO) xor CRC(0, B), O) xor CRC(0, C)
-	//             = CRC(CRC(CRC(I, A), O) xor CRC(0, B), O) xor CRC(0, C)
-	//
-	// The castagnoliSSE42Triple function can compute CRC(I, A), CRC(0, B),
-	// and CRC(0, C) efficiently.  We just need to find a way to quickly compute
-	// CRC(uvwx, O) given a 4-byte initial value uvwx. We can precompute these
-	// values; since we can't have a 32-bit table, we break it up into four
-	// 8-bit tables:
-	//
-	//    CRC(uvwx, O) = CRC(u000, O) xor
-	//                   CRC(0v00, O) xor
-	//                   CRC(00w0, O) xor
-	//                   CRC(000x, O)
-	//
-	// We can compute tables corresponding to the four terms for all 8-bit
-	// values.
-
-	crc = ^crc
-
-	// If a buffer is long enough to use the optimization, process the first few
-	// bytes to align the buffer to an 8 byte boundary (if necessary).
-	if len(p) >= castagnoliK1*3 {
-		delta := int(uintptr(unsafe.Pointer(&p[0])) & 7)
-		if delta != 0 {
-			delta = 8 - delta
-			crc = castagnoliSSE42(crc, p[:delta])
-			p = p[delta:]
-		}
-	}
-
-	// Process 3*K2 at a time.
-	for len(p) >= castagnoliK2*3 {
-		// Compute CRC(I, A), CRC(0, B), and CRC(0, C).
-		crcA, crcB, crcC := castagnoliSSE42Triple(
-			crc, 0, 0,
-			p, p[castagnoliK2:], p[castagnoliK2*2:],
-			castagnoliK2/24)
-
-		// CRC(I, AB) = CRC(CRC(I, A), O) xor CRC(0, B)
-		crcAB := castagnoliShift(castagnoliSSE42TableK2, crcA) ^ crcB
-		// CRC(I, ABC) = CRC(CRC(I, AB), O) xor CRC(0, C)
-		crc = castagnoliShift(castagnoliSSE42TableK2, crcAB) ^ crcC
-		p = p[castagnoliK2*3:]
-	}
-
-	// Process 3*K1 at a time.
-	for len(p) >= castagnoliK1*3 {
-		// Compute CRC(I, A), CRC(0, B), and CRC(0, C).
-		crcA, crcB, crcC := castagnoliSSE42Triple(
-			crc, 0, 0,
-			p, p[castagnoliK1:], p[castagnoliK1*2:],
-			castagnoliK1/24)
-
-		// CRC(I, AB) = CRC(CRC(I, A), O) xor CRC(0, B)
-		crcAB := castagnoliShift(castagnoliSSE42TableK1, crcA) ^ crcB
-		// CRC(I, ABC) = CRC(CRC(I, AB), O) xor CRC(0, C)
-		crc = castagnoliShift(castagnoliSSE42TableK1, crcAB) ^ crcC
-		p = p[castagnoliK1*3:]
-	}
-
-	// Use the simple implementation for what's left.
-	crc = castagnoliSSE42(crc, p)
-	return ^crc
+	return simpleUpdate(crc, simpleMakeTable(Castagnoli), p)
 }
```



## go/token (etcd-grove)

#### `Net/Code/go/token.toml` — model `models/go/token`, 1 replaced declarations

##### `IsExported`
```diff
--- go
+++ model
@@ -1,6 +1,27 @@
-// token.go
-// IsExported reports whether name starts with an upper-case letter.
+// model.go
+// MODEL: IsExported is, in Go, `ch, _ := utf8.DecodeRuneInString(name); return
+// unicode.IsUpper(ch)`. The model gives Go's result wherever the name's first byte is ASCII, and any result otherwise:
+//   - The empty name: DecodeRuneInString returns RuneError (U+FFFD), which is not upper case, so
+//     Go returns false, as the model does.
+//   - A first byte c < utf8.RuneSelf (0x80): DecodeRuneInString returns rune(c) (its fast path),
+//     and IsUpper of a rune <= MaxLatin1 is properties[uint8(r)]&pLmask == pLu
+//     (unicode/letter.go), which for c < 0x80 holds exactly of 'A'..'Z' (unicode/tables.go's
+//     properties table). The model returns 'A' <= c && c <= 'Z'.
+//   - Any other first byte: Go's result is IsUpper of the decoded rune (RuneError for an invalid
+//     encoding) and depends on Unicode's case tables. The model returns gomodel.Choose(), any
+//     boolean, which covers both of Go's possible results.
+//
+// It reads no package variable, which is why it stands in for Go's code: that code is
+// translatable (goose translates it, with unicode's tables), but IsUpper reads unicode's tables
+// and DecodeRuneInString's slow path reads utf8's, so a proof of Go's code needs those packages'
+// initialization, which IsExported's spec does not take.
 func IsExported(name string) bool {
-	ch, _ := utf8.DecodeRuneInString(name)
-	return unicode.IsUpper(ch)
+	if len(name) == 0 {
+		return false
+	}
+	c := name[0]
+	if c < utf8.RuneSelf {
+		return 'A' <= c && c <= 'Z'
+	}
+	return gomodel.Choose()
 }
```



## net (etcd-grove)

#### `Net/Code/net.toml` — model `models/net`, 20 replaced declarations

##### `netFD.Read`
```diff
--- go
+++ model
@@ -1,6 +1,15 @@
-// fd_posix.go
+// model.go
+// MODEL: netFD.Read (fd_posix.go: `fd.pfd.Read(p)`, poll.FD's loop over read(2) through the
+// poller, wrapped by wrapSyscallError("read")): the extension's Read of len(p) bytes (D1, the
+// outcomes of Linux's read(2) with Go's poller), the bytes copied into p; 0 bytes from a
+// non-empty p is io.EOF, as poll.FD's ZeroReadIsEOF; an error is the kind's (codeKindErr).
 func (fd *netFD) Read(p []byte) (n int, err error) {
-	n, err = fd.pfd.Read(p)
-	runtime.KeepAlive(fd)
-	return n, wrapSyscallError(readSyscallName, err)
+	s, code := extRead(fd.pfd.Sysfd, len(p))
+	if code == 0 {
+		return copy(p, []byte(s)), nil
+	}
+	if code == 4 {
+		return 0, io.EOF
+	}
+	return 0, codeKindErr(code, "read")
 }
```

##### `netFD.Write`
```diff
--- go
+++ model
@@ -1,6 +1,17 @@
-// fd_posix.go
+// model.go
+// MODEL: netFD.Write (fd_posix.go, poll.FD.Write's loop): a write(2) of p[nn:] with its wait is
+// one step of the extension's Write (D2), which says whether it is the call's first (D25: the
+// end's write lock, Go's fd.writeLock()), until a step fails or every byte is written. Go's
+// maxRW chunks are among a step's outcomes (any prefix).
 func (fd *netFD) Write(p []byte) (nn int, err error) {
-	nn, err = fd.pfd.Write(p)
-	runtime.KeepAlive(fd)
-	return nn, wrapSyscallError(writeSyscallName, err)
+	for {
+		n, code := extWrite(fd.pfd.Sysfd, string(p[nn:]), nn == 0)
+		nn += n
+		if code != 0 {
+			return nn, codeKindErr(code, "write")
+		}
+		if nn == len(p) {
+			return nn, nil
+		}
+	}
 }
```

##### `netFD.Close`
```diff
--- go
+++ model
@@ -1,6 +1,6 @@
-// fd_posix.go
+// model.go
+// MODEL: netFD.Close (fd_posix.go, poll.FD.Close): the extension's Close (D3: success, or
+// `closed` for a second close; Linux's close(2) of a socket does not fail).
 func (fd *netFD) Close() error {
-	// TODO Replace with runtime.AddCleanup.
-	runtime.SetFinalizer(fd, nil)
-	return fd.pfd.Close()
+	return codeErr(extClose(fd.pfd.Sysfd), "close")
 }
```

##### `netFD.closeWrite`
```diff
--- go
+++ model
@@ -1,4 +1,6 @@
-// fd_posix.go
+// model.go
+// MODEL: netFD.closeWrite (fd_posix.go: shutdown(2) with SHUT_WR, wrapSyscallError("shutdown")):
+// the extension's CloseWrite (D4).
 func (fd *netFD) closeWrite() error {
-	return fd.shutdown(syscall.SHUT_WR)
+	return codeErr(extCloseWrite(fd.pfd.Sysfd), "shutdown")
 }
```

##### `netFD.SetDeadline`
```diff
--- go
+++ model
@@ -1,4 +1,6 @@
-// fd_posix.go
+// model.go
+// MODEL: netFD.SetDeadline (fd_posix.go, poll.FD.SetDeadline): the extension's SetDeadline of
+// both deadlines (D5; the zero time clears them).
 func (fd *netFD) SetDeadline(t time.Time) error {
-	return fd.pfd.SetDeadline(t)
+	return codeErr(extSetDeadline(fd.pfd.Sysfd, 0, t), "set")
 }
```

##### `netFD.SetReadDeadline`
```diff
--- go
+++ model
@@ -1,4 +1,5 @@
-// fd_posix.go
+// model.go
+// MODEL: netFD.SetReadDeadline: the read deadline only (D5).
 func (fd *netFD) SetReadDeadline(t time.Time) error {
-	return fd.pfd.SetReadDeadline(t)
+	return codeErr(extSetDeadline(fd.pfd.Sysfd, 1, t), "set")
 }
```

##### `netFD.SetWriteDeadline`
```diff
--- go
+++ model
@@ -1,4 +1,5 @@
-// fd_posix.go
+// model.go
+// MODEL: netFD.SetWriteDeadline: the write deadline only (D5).
 func (fd *netFD) SetWriteDeadline(t time.Time) error {
-	return fd.pfd.SetWriteDeadline(t)
+	return codeErr(extSetDeadline(fd.pfd.Sysfd, 2, t), "set")
 }
```

##### `netFD.accept`
```diff
--- go
+++ model
@@ -1,19 +1,11 @@
-// fd_unix.go
+// model.go
+// MODEL: netFD.accept (fd_unix.go: accept4(2) through the poller, ECONNABORTED retried, errors
+// wrapped by wrapSyscallError("accept4")): the extension's Accept (D7); the new socket's addresses
+// arbitrary (D18), its network the listener's (Go's newFD(d, fd.family, fd.sotype, fd.net)).
 func (fd *netFD) accept() (netfd *netFD, err error) {
-	d, rsa, errcall, err := fd.pfd.Accept()
-	if err != nil {
-		if errcall != "" {
-			err = wrapSyscallError(errcall, err)
-		}
-		return nil, err
+	id, code := extAccept(fd.pfd.Sysfd)
+	if code != 0 {
+		return nil, codeKindErr(code, "accept4")
 	}
-
-	netfd = newFD(d, fd.family, fd.sotype, fd.net)
-	if err = netfd.init(); err != nil {
-		netfd.Close()
-		return nil, err
-	}
-	lsa, _ := syscall.Getsockname(netfd.pfd.Sysfd)
-	netfd.setAddr(netfd.addrFunc()(lsa), netfd.addrFunc()(rsa))
-	return netfd, nil
+	return modelFD(id, fd.net, anyTCPAddr(), anyTCPAddr()), nil
 }
```

##### `setReadBuffer`
```diff
--- go
+++ model
@@ -1,6 +1,6 @@
-// sockopt_posix.go
+// model.go
+// MODEL: setReadBuffer (sockopt_posix.go: SO_RCVBUF, wrapSyscallError("setsockopt")): the
+// extension's SetSockopt of an option of no validity condition (D24; Linux clamps the value).
 func setReadBuffer(fd *netFD, bytes int) error {
-	err := fd.pfd.SetsockoptInt(syscall.SOL_SOCKET, syscall.SO_RCVBUF, bytes)
-	runtime.KeepAlive(fd)
-	return wrapSyscallError("setsockopt", err)
+	return codeErr(extSetSockopt(fd.pfd.Sysfd, 0, 0), "setsockopt")
 }
```

##### `setWriteBuffer`
```diff
--- go
+++ model
@@ -1,6 +1,5 @@
-// sockopt_posix.go
+// model.go
+// MODEL: setWriteBuffer (SO_SNDBUF), as setReadBuffer.
 func setWriteBuffer(fd *netFD, bytes int) error {
-	err := fd.pfd.SetsockoptInt(syscall.SOL_SOCKET, syscall.SO_SNDBUF, bytes)
-	runtime.KeepAlive(fd)
-	return wrapSyscallError("setsockopt", err)
+	return codeErr(extSetSockopt(fd.pfd.Sysfd, 0, 0), "setsockopt")
 }
```

##### `setKeepAlive`
```diff
--- go
+++ model
@@ -1,6 +1,5 @@
-// sockopt_posix.go
+// model.go
+// MODEL: setKeepAlive (SO_KEEPALIVE), whatever the value (D24).
 func setKeepAlive(fd *netFD, keepalive bool) error {
-	err := fd.pfd.SetsockoptInt(syscall.SOL_SOCKET, syscall.SO_KEEPALIVE, boolint(keepalive))
-	runtime.KeepAlive(fd)
-	return wrapSyscallError("setsockopt", err)
+	return codeErr(extSetSockopt(fd.pfd.Sysfd, 0, 0), "setsockopt")
 }
```

##### `setLinger`
```diff
--- go
+++ model
@@ -1,14 +1,5 @@
-// sockopt_posix.go
+// model.go
+// MODEL: setLinger (SO_LINGER), whatever the value (D24: a resetting Close is a cut, D1).
 func setLinger(fd *netFD, sec int) error {
-	var l syscall.Linger
-	if sec >= 0 {
-		l.Onoff = 1
-		l.Linger = int32(sec)
-	} else {
-		l.Onoff = 0
-		l.Linger = 0
-	}
-	err := fd.pfd.SetsockoptLinger(syscall.SOL_SOCKET, syscall.SO_LINGER, &l)
-	runtime.KeepAlive(fd)
-	return wrapSyscallError("setsockopt", err)
+	return codeErr(extSetSockopt(fd.pfd.Sysfd, 0, 0), "setsockopt")
 }
```

##### `setNoDelay`
```diff
--- go
+++ model
@@ -1,6 +1,5 @@
-// tcpsockopt_posix.go
+// model.go
+// MODEL: setNoDelay (tcpsockopt_posix.go: TCP_NODELAY), whatever the value (D24).
 func setNoDelay(fd *netFD, noDelay bool) error {
-	err := fd.pfd.SetsockoptInt(syscall.IPPROTO_TCP, syscall.TCP_NODELAY, boolint(noDelay))
-	runtime.KeepAlive(fd)
-	return wrapSyscallError("setsockopt", err)
+	return codeErr(extSetSockopt(fd.pfd.Sysfd, 0, 0), "setsockopt")
 }
```

##### `setKeepAliveIdle`
```diff
--- go
+++ model
@@ -1,14 +1,7 @@
-// tcpsockopt_unix.go
+// model.go
+// MODEL: setKeepAliveIdle (tcpsockopt_unix.go: TCP_KEEPIDLE of d rounded up to seconds, the
+// default for 0, nothing for d < 0): the extension's SetSockopt of kind 1 with d, whose
+// arithmetic the extension's keepIdleValid transcribes (D24).
 func setKeepAliveIdle(fd *netFD, d time.Duration) error {
-	if d == 0 {
-		d = defaultTCPKeepAliveIdle
-	} else if d < 0 {
-		return nil
-	}
-
-	// The kernel expects seconds so round to next highest second.
-	secs := int(roundDurationUp(d, time.Second))
-	err := fd.pfd.SetsockoptInt(syscall.IPPROTO_TCP, syscall.TCP_KEEPIDLE, secs)
-	runtime.KeepAlive(fd)
-	return wrapSyscallError("setsockopt", err)
+	return codeErr(extSetSockopt(fd.pfd.Sysfd, 1, int64(d)), "setsockopt")
 }
```

##### `TCPListener.accept`
```diff
--- go
+++ model
@@ -1,3 +1,7 @@
-// tcpsock_posix.go
+// model.go
+// MODEL: TCPListener.accept (tcpsock_posix.go): Go's code but newTCPConn's setup of the new
+// connection (TCP_NODELAY and the listener's keep-alive options, their errors ignored by Go; what
+// they change in the kernel is not observable beyond D1's cuts, D24), and with it its reads of
+// the test hooks testPreHookSetKeepAlive and testHookSetKeepAlive (nil outside net's tests).
 func (ln *TCPListener) accept() (*TCPConn, error) {
 	fd, err := ln.fd.accept()
@@ -5,4 +9,4 @@
 		return nil, err
 	}
-	return newTCPConn(fd, ln.lc.KeepAlive, ln.lc.KeepAliveConfig, testPreHookSetKeepAlive, testHookSetKeepAlive), nil
+	return &TCPConn{conn{fd}}, nil
 }
```

##### `TCPListener.close`
```diff
--- go
+++ model
@@ -1,4 +1,6 @@
-// tcpsock_posix.go
+// model.go
+// MODEL: TCPListener.close (tcpsock_posix.go: ln.fd.Close(), close(2) of the listening socket):
+// the extension's LisClose (D9), the extension's operation on a listener.
 func (ln *TCPListener) close() error {
-	return ln.fd.Close()
+	return codeErr(extLisClose(ln.fd.pfd.Sysfd), "close")
 }
```

##### `Listen`
```diff
--- go
+++ model
@@ -1,26 +1,18 @@
-// dial.go
-// Listen announces on the local network address.
-//
-// The network must be "tcp", "tcp4", "tcp6", "unix" or "unixpacket".
-//
-// For TCP networks, if the host in the address parameter is empty or
-// a literal unspecified IP address, Listen listens on all available
-// unicast and anycast IP addresses of the local system.
-// To only use IPv4, use network "tcp4".
-// The address can use a host name, but this is not recommended,
-// because it will create a listener for at most one of the host's IP
-// addresses.
-// If the port in the address parameter is empty or "0", as in
-// "127.0.0.1:" or "[::1]:0", a port number is automatically chosen.
-// The [Addr] method of [Listener] can be used to discover the chosen
-// port.
-//
-// See func [Dial] for a description of the network and address
-// parameters.
-//
-// Listen uses context.Background internally; to specify the context, use
-// [ListenConfig.Listen].
+// model.go
+// MODEL: Listen (dial.go: ListenConfig.Listen with the zero ListenConfig: the address resolved,
+// socket(2), setsockopt, bind(2), listen(2)): for "tcp" and "tcp4" (D23; any other network is not
+// modelled: stuck), the extension's Listen of the address (D6); the listener's address arbitrary
+// (D18); an error is Go's `&OpError{Op: "listen", Net: network, Addr: <the resolved address>}`,
+// the address arbitrary (anyListenAddr: with a nil IP too, Go's for ":p") and the failing system
+// call's name too (any of Go's).
 func Listen(network, address string) (Listener, error) {
-	var lc ListenConfig
-	return lc.Listen(context.Background(), network, address)
+	if !netOk(network) {
+		stuck()
+	}
+	id, code := extListen(address)
+	if code == 0 {
+		return &TCPListener{fd: modelFD(id, network, anyTCPAddr(), nil)}, nil
+	}
+	return nil, &OpError{Op: "listen", Net: network, Source: nil, Addr: anyListenAddr(),
+		Err: codeKindErr(code, extAnyString())}
 }
```

##### `Dial`
```diff
--- go
+++ model
@@ -1,53 +1,16 @@
-// dial.go
-// Dial connects to the address on the named network.
-//
-// Known networks are "tcp", "tcp4" (IPv4-only), "tcp6" (IPv6-only),
-// "udp", "udp4" (IPv4-only), "udp6" (IPv6-only), "ip", "ip4"
-// (IPv4-only), "ip6" (IPv6-only), "unix", "unixgram" and
-// "unixpacket".
-//
-// For TCP and UDP networks, the address has the form "host:port".
-// The host must be a literal IP address, or a host name that can be
-// resolved to IP addresses.
-// The port must be a literal port number or a service name.
-// If the host is a literal IPv6 address it must be enclosed in square
-// brackets, as in "[2001:db8::1]:80" or "[fe80::1%zone]:80".
-// The zone specifies the scope of the literal IPv6 address as defined
-// in RFC 4007.
-// The functions [JoinHostPort] and [SplitHostPort] manipulate a pair of
-// host and port in this form.
-// When using TCP, and the host resolves to multiple IP addresses,
-// Dial will try each IP address in order until one succeeds.
-//
-// Examples:
-//
-//	Dial("tcp", "golang.org:http")
-//	Dial("tcp", "192.0.2.1:http")
-//	Dial("tcp", "198.51.100.1:80")
-//	Dial("udp", "[2001:db8::1]:domain")
-//	Dial("udp", "[fe80::1%lo0]:53")
-//	Dial("tcp", ":80")
-//
-// For IP networks, the network must be "ip", "ip4" or "ip6" followed
-// by a colon and a literal protocol number or a protocol name, and
-// the address has the form "host". The host must be a literal IP
-// address or a literal IPv6 address with zone.
-// It depends on each operating system how the operating system
-// behaves with a non-well known protocol number such as "0" or "255".
-//
-// Examples:
-//
-//	Dial("ip4:1", "192.0.2.1")
-//	Dial("ip6:ipv6-icmp", "2001:db8::1")
-//	Dial("ip6:58", "fe80::1%lo0")
-//
-// For TCP, UDP and IP networks, if the host is empty or a literal
-// unspecified IP address, as in ":80", "0.0.0.0:80" or "[::]:80" for
-// TCP and UDP, "", "0.0.0.0" or "::" for IP, the local system is
-// assumed.
-//
-// For Unix networks, the address must be a file system path.
+// model.go
+// MODEL: Dial (dial.go: Dialer.Dial with the zero Dialer: the address resolved, socket(2),
+// connect(2) and the handshake's wait): for "tcp" and "tcp4" (D23), the extension's Dial (D8,
+// D16); the connection's addresses arbitrary (D18); an error is Go's `&OpError{Op: "dial", Net:
+// network, Addr: <the resolved address>}` (dialSingle), as Listen's.
 func Dial(network, address string) (Conn, error) {
-	var d Dialer
-	return d.Dial(network, address)
+	if !netOk(network) {
+		stuck()
+	}
+	id, code := extDial(address)
+	if code == 0 {
+		return newConn(id, network), nil
+	}
+	return nil, &OpError{Op: "dial", Net: network, Source: nil, Addr: anyTCPAddr(),
+		Err: codeKindErr(code, extAnyString())}
 }
```

##### `DialTimeout`
```diff
--- go
+++ model
@@ -1,15 +1,23 @@
-// dial.go
-// DialTimeout acts like [Dial] but takes a timeout.
-//
-// The timeout includes name resolution, if required.
-// When using TCP, and the host in the address parameter resolves to
-// multiple IP addresses, the timeout is spread over each consecutive
-// dial, such that each is given an appropriate fraction of the time
-// to connect.
-//
-// See func Dial for a description of the network and address
-// parameters.
+// model.go
+// MODEL: DialTimeout (dial.go: Dialer{Timeout: timeout}.Dial), as Dial (D19); a failure's Err is
+// the system's error or a timeout: errTimeout (mapErr(ctx.Err()) once the dial's context expired)
+// or poll.ErrDeadlineExceeded (netFD.connect's wait under the dial's deadline). The timeout's value
+// is not modelled (any timeout may expire, as D5's deadlines).
 func DialTimeout(network, address string, timeout time.Duration) (Conn, error) {
-	d := Dialer{Timeout: timeout}
-	return d.Dial(network, address)
+	if !netOk(network) {
+		stuck()
+	}
+	id, code := extDial(address)
+	if code == 0 {
+		return newConn(id, network), nil
+	}
+	var err error
+	if extAnyBool() {
+		err = codeKindErr(code, extAnyString())
+	} else if extAnyBool() {
+		err = errTimeout
+	} else {
+		err = poll.ErrDeadlineExceeded
+	}
+	return nil, &OpError{Op: "dial", Net: network, Source: nil, Addr: anyTCPAddr(), Err: err}
 }
```

##### `TCPAddr.String`
```diff
--- go
+++ model
@@ -1,11 +1,7 @@
-// tcpsock.go
+// model.go
+// MODEL: TCPAddr.String (tcpsock.go: JoinHostPort of ipEmptyString(a.IP), the zone and the port;
+// IP.String formats through net/netip, which nothing translates): an arbitrary string. Go's
+// String always returns (a nil receiver gives "<nil>"), with no other effect.
 func (a *TCPAddr) String() string {
-	if a == nil {
-		return "<nil>"
-	}
-	ip := ipEmptyString(a.IP)
-	if a.Zone != "" {
-		return JoinHostPort(ip+"%"+a.Zone, strconv.Itoa(a.Port))
-	}
-	return JoinHostPort(ip, strconv.Itoa(a.Port))
+	return extAnyString()
 }
```

Model-only declarations (additions, stubs; no real counterpart is replaced): `anyListenAddr`, `anyTCPAddr`, `codeErr`, `codeKindErr`, `detach`, `errnoCode`, `extAccept`, `extAnyBool`, `extAnyErrno`, `extAnyString`, `extAnyW64`, `extClose`, `extCloseWrite`, `extDial`, `extLisClose`, `extListen`, `extRead`, `extSetDeadline`, `extSetSockopt`, `extWrite`, `modelFD`, `netClosingErr`, `netOk`, `newConn`, `stuck`



# Statement and premise changes

No top-level theorem gains a premise; no new axiom (tcb-report below). Removed premises:
`[os.file.FieldAssumptions]`, `[os.fileStat.FieldAssumptions]` (169 files, incl. the etcd/k8s/bboltfs/walfs/kvnet
top-level results), `[net.FieldAssumptions]` (549 files, incl. 13 top-level results). Internal spec changes
(preconditions of library results, discharged by every caller):
- net `Conn.Read`/`Conn.Read.specLc` take `isPkgInit io ∗ isPkgInit internal.poll`; `Conn.Write` takes
  `isPkgInit internal.poll` (lead's decision: Go's `conn.Read` compares with `io.EOF`); the connection's
  `fdAt` now carries `isPkgInit net`, from which both are derived, so callers pass nothing new.
- net `OpError.Timeout/Temporary` specs and `wp_OpError_Error` take `opErrOk`/`opErrMsgOk` (your D2); `errStr e`
  is conditional on `syscall.errnoOk` (`Errno.Error` is translated and reads syscall's table).
- `isPkgInit net` added to `net.Dial.spec`, `net.DialTimeout.spec`, `net.Listen.spec`, `Listen.specAddrOk`,
  `net.rpc.Dial.spec`, `rpc.DialHTTPPath.spec`, `rpc.DialHTTP.spec`, Dsverify lab `net.Dial/Listen.labProof(U)`,
  main `EtcdGrove.net.Listen.spec`; every caller derives it (its own package imports net). Dsverify's
  undischarged `RpcHttpHyp.DialHTTPPath_spec` keeps its old precondition.
- `http.ReadResponse.spec`: the stream-error law and the error post use `net.errStr`; stronger post.
- log: none (2026-11-25: `log.Println`/`Printf` trusted as on lean again; Net's `log.Println.spec` as on lean).
- os: `rawConn.Control/Read/Write` names-only (were trusted-panicking on lean): no spec named them.
- (2026-11-25, os review fix) `os.Open/OpenFile.wp_dirS`, `wp_dirErrS`, `wp_dirChildS` give `os.ownOff f 0`;
  `os.File.Readdirnames.wp_dirS`/`wp_dirChildS` take it (and consume it: the offset is unknown after);
  `fileutil.ReadDir.wp_core`'s abstract `Fd` takes the `*File`. Internal; no caller outside os/fileutil/WAL/walfs.

# Decisions taken without you (check each)
1. Printf's stdout write stays trusted as on lean (coordinator's "option 0"): a Go model of it needs a
   semantics primitive choosing an arbitrary interface value; fmt then imports no io/fs/poll/syscall, which
   etcd-grove translates itself under the same `Perennial.*` names. See criterion 14 below: its error's type.
2. fmt models `pp.doPrintln` exactly like `pp.doPrint` (the model printer); Go's real doPrintln calls
   printArg, whose proof covers only a subset. (Kept after log went back to lean's trusted model: it is what
   log.Println's future Go model will use.)
3. os review fixes: `Seek` is stuck on SEEK_DATA/SEEK_HOLE, past `modelSeekMax` on a directory, SEEK_END on a
   directory, SEEK_CUR after `Readdirnames` (offset unknown); `Readdirnames` is stuck unless the offset is 0.
4. os/net: GooseLang has no GC, so `newFile`'s and `netFD`'s finalizers (closing an unreachable, unclosed
   `*File`'s fd, releasing its flock; closing a dropped listener, so a second `Listen` at its address succeeds
   in Go) are not covered — as on lean (the old Lean models did not cover them either). Options: an
   environment premise, or a semantics change (rule #8: needs your OK).
5. `ownFile` gains `nonblock ↦□ false` and `appendMode ↦□ false` (Go's `fd()`/`readFrom` read them).
6. `x/sys/unix` stays hand-written Lean (not std: no `internal/gomodel`; `Mmap` returns `unsafe.Pointer`).

# Open (known divergences, not fixed)
- **log.Println/Printf** trusted as on lean (decided above; gap analysis below; retirement after reflection S0+S0.5).
- **No GC** (decision 4): unreachable `*File` / dropped listener close.
- **Readdirnames offset**: the model does not follow a directory's offset; it is now stuck wherever Go's
  answer depends on it (Seek SEEK_CUR after Readdirnames, SEEK_END of a directory, Readdirnames from a nonzero
  offset): sound, less defined. `n > 0` and a second Readdirnames on one fd stay stuck as before.
- **Size** of the fmt model printer and the os model (above).
- durable: name aliasing (`"./x"` vs `"x"`) and `.durable-` temporaries visible to Go's `Read` after a crash
  (documented in `GooseLang/Ext/Durable/Impl.lean` as accepted). New (review 2): durable's files are also
  `os` files in Go, but `durableExt` and `fsExt` keep separate state; no proved program uses both on one file
  (kvdurable/kvfile use durable only). To state in Impl.lean's divergence list. Also: Go's out-of-memory on a
  huge `Read` is listed there as "model more defined"; it is the framework-wide "allocation never fails".
- net: `StructFieldRef` of a nil `*TCPConn` (a promoted method on a nil receiver) does not panic in Perennial's
  semantics (`PostLang.lean`'s FIXME); Go panics. Stuck in practice (no proof reaches it); a Perennial fix.
- net: the extension's D12 excludes a failed `epoll_ctl` registration (Go's bare `syscall.Errno` from
  `Accept`/`Dial`, `ENOMEM`/`ENOSPC`): a criterion-14 exclusion (below).
- Perennial: no `go.NotInterface` instance for predeclared named types (`uintptr`); net's proof adds a local one.

# The `log.Println` gap (lean's trusted model; issue text, for coordinator-E to post)
**Title:** Trusted `log.Println`/`log.Printf` do not call the arguments' `String`/`Error`/`Format` methods (documented gap; no proof affected)

**Body:**

Perennial's `log.Println` and `log.Printf` (`Perennial/TrustedCode/log.lean`, on `lean`) are trusted with the model `λ args, #()`: they do nothing. Real Go formats the arguments through fmt, and fmt calls user code on them:

- `Format(fmt.State, rune)` for every verb except `%T`/`%p`;
- `Error() string` or `String() string` for `%v %s %x %X %q` and for every `Println` operand;
- `GoString()` for `%#v`.

fmt also calls these on the elements it visits: struct fields, slice/array/map elements, and the struct behind a pointer at depth 0. User code that blocks, mutates shared state, races or does not terminate therefore runs in Go but not in the model. A proof that steps the no-op over such an argument could prove a program safe that is not.

**Who reaches it today (etcd-grove at `go-models-rest-egnet/2026-11-24` 4313327873, all Code roots):** no proved path passes such an argument.

- **Through specs that require `fmt.ArgsWf`.** These are `log.Printf.spec` (Perennial) and Net's `log.Println.spec`. `ArgsWf` admits only basic types, or named int/string types with `NoFmtMethods`.
  - paxos: acceptor `receivePrepare`/`receivePropose`, learner `learn`/`receiveAccepted`, proposer `run`/`receivePromise`. All are `%d`/`%s` of int and string. They reach `paxos_remote_robust`.
  - swiftnet: `configure` (one string) and `Sys.changeLeaders` (`%d` of uint64). They reach `swiftpaxos_remote_robust`.
  - rabianet `send`: one string. Reaches `rabia_remote_robust`.
  - net/rpc `Server.Accept`: one string, built with an explicit, verified `err.Error()`.
- **Through local lemmas over the no-op.**
  - quepaxanet `KitConf.wp_log_Println` takes a single string.
  - swift `wp_PrintlnT` with the guard `swift.printable` covers `Replica.handleNewLeader` (string, int32) and `Replica.handleSync`. The latter prints string, int32 and int64 arguments, and `FQ`/`SQ` whose dynamic types are `replica.Quorum = map[int32]struct{}`, `Majority` or `ThreeQuarters` (int). Their method sets are only Contains/Size/Equals/copy, and the elements `int32`/`struct{}` have none.
- **Not reached.**
  - net/rpc `Client.input`, `Server.sendResponse` and `Server.ServeCodec` print an `error` operand, which is exactly the gap. They sit behind `debugLog`, which the proofs hold false (`Net/Proof/net/rpc/ClientDefs.lean:101`).
  - The `Server.register` logging branches are excluded by its premises. `ServeHTTP` is proved only on a successful hijack.
  - paxos `paxosNetwork.send`/`empty`/`recvFrom` and net/http `Server.logf` have no proof.
  - The `dlog` loggers' specs require a quiet logger, which prints nothing in Go as well.

**Weak spot.** `swift.printable` checks only the operand's own method set, not the elements fmt would visit. It is sound for its four current uses, but it would admit a bad argument if reused. Replacing it with `fmt.ArgsWf` plus a no-method lemma for the quorum types would close that.

**Plan.** The trusted model stays as on `lean` (decision in etcd-grove#8 7153952113). The model will be retired once reflection S0+S0.5 is approved: fmt's model printer then follows maps, using the reflect models. After that, `log.Println`/`Printf` become Go models over `fmt.Fprintln`/`Fprintf` again (the Perennial `goose-model-overlay-rest` design before d81d2bfd8), and this gap closes. Until then, every new proof that reaches `log.Print*` must take a spec with `fmt.ArgsWf` (or an equivalent no-method premise), never the bare no-op.

# Adversarial reviews (fresh agents, code only)
- (2026-11-25) decision (b), `os` without `runtime` (code: `4313327873`): no divergence. `*rawConn`'s method
  set is unchanged (only the unfolds and bodies are gone), so `SyscallConn`'s conversion and
  `getPollFDAndNetwork`'s `PollFD` assertion (false, as in Go: Proof/io/CopyFiles.lean:102, CopyFrom.lean:185)
  behave as before; no proof used the three methods. os's initializer reads nothing of runtime; packages that
  reach runtime by another path (zap, klog, bbolt, rafthttp, net/http) still initialize it. `Process` is an
  opaque type with generated `sorry -- axiomatized type` instances, identical to lean's. DOC: kvwitness's
  hand-written `pkgInitTable` still listed runtime -> fixed (`RaftWitness/.../kvwitness/Adequacy.lean`).
Round 1 (2026-11-25 early):
- egos: UNSOUND Seek(3|4), UNSOUND directory seek limit -> fixed; directory offset -> open; finalizer ->
  framework gap; syscall: no divergence; DOC fixes done.
- egnet: UNSOUND-but-framework: the dropped-listener finalizer (above, demo `adv-egnet/gcl/main.go`). DOC: stale
  references to the old trusted net model in `GooseLang/Ext/Net/Impl.lean`.
Round 2 (2026-11-25, after sessions 7-8; demos in `tmp/gomodels/adv2-egos/`, `adv2-egnet/`):
- egos: **UNSOUND** `Seek(0, SEEK_CUR)` of a directory after `Readdirnames` (Go, ext4: 2^63-1; model: 0)
  -> **FIXED** `d2fa9c8519` (with SEEK_END of a directory, found while fixing: Go answers the htree's end,
  2^63-1, the model the size; evidence `examples/osfs/semantics/model_os_dir_offset.go`, `TestDirOffset`).
  Conditional UNSOUND: durable vs os state (open, above). DOC: zero `File`'s "dereference nil" is stuck in the
  model, not a recoverable panic -> comment fixed. Everything else no divergence (OpenFile, Close, ReadAt,
  WriteAt, Write, Read, Seek on files, Stat, Truncate, Sync, Rename, Readdirnames(n<=0), Stat/Lstat,
  RemoveAll, copyFileRange; syscall's models).
- egnet: **UNSOUND** `Listen`'s error `Addr`: Go's for `":p"` has a nil IP (`&TCPAddr{Port: p}`), the model's
  `anyTCPAddr` never does -> **FIXED** `62c7668c97` (`anyListenAddr`). Latent: nil `*TCPConn` promoted methods
  (Perennial `StructFieldRef`, above). DOC: Impl.lean's stale references (not changed: a docstring edit
  rebuilds every Net module). Everything else no divergence, incl. criterion 14 (below); IMPRECISE, intended:
  DialTimeout(0) may time out, negative timeout may succeed, any deadline may expire, `TCPAddr.String`
  nondeterministic.
- Earlier rounds: split, rt, egrest (no unsafe divergence left; rt's ChooseStrings fixed), fmt (pooled-buffer
  aliasing fixed), sync (Cond.Wait fixed).

# Criterion 14 (a model keeps every observable dynamic type)
Audited 2026-11-25 (fmt/log/syscall by the lead; os/syscall/durable and net by the round-2 reviewers):
- fmt: `errorf` returns Go's types (`*errors.errorString`, `*wrapError`, `*wrapErrors`), the wrapped errors
  Go's (none when the model gave up: then every argument is inert, i.e. no error). User methods see no model
  type (`Format`/`GoString` are stuck, `Error`/`String` called on the user's value). **Deviation:** the trusted
  `Printf` returns `errors.New(arbitraryString())` (`*errors.errorString`) where Go returns `os.Stdout.Write`'s
  `*fs.PathError` (with a `syscall.Errno` or `poll` error inside): `errors.As(err, &pe)` differs. As on lean
  (decision 1; needs the arbitrary-interface primitive to fix, or a `layoutModelled`-style opaque type).
- log: `Printf`/`Println` return nothing; `modelDiscard` is seen only by fmt's `Fprintf`/`Fprintln`. OK.
- syscall (Perennial) `prlimit1`: `errnoErr(Errno)`, Go's values. OK.
- os/syscall/durable: every error is Go's type (`*fs.PathError` of a `syscall.Errno`, `*LinkError`,
  `*SyscallError` via the translated `wrapSyscallError`, `*errors.errorString` "negative offset", `io.EOF`,
  `ErrInvalid`, `ErrClosed`); `Op`/`Path` match Go's everywhere. OK.
- net: errors `*OpError{Err: *os.SyscallError{Errno} | poll.ErrNetClosing (errNetClosing{}) |
  poll.ErrDeadlineExceeded | errTimeout}`, `io.EOF`; `Conn`/`Listener` hold `*TCPConn`/`*TCPListener`, nil on
  failure; addresses non-nil `*TCPAddr` (a listener's `raddr` nil), `Listen`'s error address with a nil IP
  since the fix. **Exclusion:** Go's bare `syscall.Errno` from a failed `epoll_ctl` registration (resource
  exhaustion, the extension's D12).

# Evidence
- Perennial 30102d8b2: full library build int-full7 EXIT 0; `#print axioms` of the 241 linked theorems of
  bytes, errors, fmt, internal/{bytealg,gomodel,stringslite,sync}, log, os, runtime, strings, sync, syscall,
  time: `[propext, Classical.choice, Quot.sound]` only, except lean's own `strings.Fields.wp_proof`
  (`axioms-integration.txt`). `etc/trusted-delta.py` vs the basic slice: `trusted-delta-rest-vs-basic.md`
  (TrustedCode/fmt.lean −4053/+54, log −30/+4, syscall −70/+7).
- **(2026-11-25, session 10, after both decisions)** Perennial `d81d2bfd8`: full library + PerennialMeta,
  4 chunks (int-full10/10b), **every chunk EXIT 0** (chunk 01 re-run after a VM preemption). model-tests pass. etcd-grove egnet `16e82ffff7`
  (pin `d81d2bfd8`): `lake build` (all default targets) **EXIT 0, 28094 jobs, no failure** (SyncTail included;
  `tmp/gomodels/s10/eg-full12.log`). Base: lean merge-base `622264bf5e`, rebuilt from scratch (its sync dir
  was evicted), EXIT 0, 28040 jobs (`s10/base-full.log`).
- **tcb-report before/after, no exclusion** (`s10/tcb-{base,egnet}.txt`, compared by `scratch/tcbcmp.py`): roots
  8399 / 8399; `sorry` 0 / 0; this repository's axioms 329 / 329, **every one used by the same number of roots**
  (incl. `runtime.opaqueInitsOk`, `runtime.initFuncsOk`, `internal.runtime.sys.opaqueInitsOk`: 11 / 11); Perennial's
  axioms 0 / 0; results 1119 / 1119, **every result with the same `sorry`/repo-axiom/Perennial-axiom counts**: the
  30 results of the session-9 regression are back at their lean axiom sets. RaftNoAx's
  `raft_kvdurable_porcupine_robust`: 0 axioms; `tcb-report --collection etc/tcb-collections/raft-noax.txt --check`:
  "trust base matches (0 axioms, 0 sorries)". Definitions 18790 / 18802 (+12, net's `Base.lean` and its helpers).
- (superseded by the above) session 9's reports, kept for the record:
- etcd-grove builds: egnet-full (55c465fab3, before this session's fixes) and egnet-os3 (4527ef62a8, with them): `lake build` (all default targets, 28111 jobs) EXIT 1 with exactly one failing module, Dsverify swiftpaxos `SyncTail` (PENDING log.Println); everything else built, incl. every module the 2026-11-25 fixes touched (os NsS/NsChildS/NsSOk/Off/OffEnd, fileutil ReadDir*, WAL ExistCallees, walfs DSBase/DSCheck, durable tryWrite in WalTester/KvNet, Net/KvNet net Errors/Listen and their importers). Logs `tmp/gomodels/s9/`.
- tcb-report before/after: `etc/tcb-report.py`, **before** = lean merge-base `622264bf5e` (Perennial `d9c8c1d97`, full build EXIT 0), **after** = egnet `4527ef62a8` (Perennial `30102d8b2`); both with the 3 root modules that import `SyncTail` excluded (swiftpaxos `swift/Results`, `examples/swiftnet/Link`, `.../swiftnet/TopLevelRobustness`; a VM-side temporary filter in `etc/proof_roots.py`, not committed), so both cover the same 8369 roots:
  - `sorry`: 0 / 0. This repository's axioms: 329 / 329, **the same names** (none added, none removed). Perennial's axioms 0 / 0. Results 1129 / 1129 with the same statements' files; definitions 18791 / 18803 (+12: `Net/Proof/net/Base.lean` +6 (`errStr`, `fdAt` with `isPkgInit net`, ...), `Spec/hash/crc32/Model.lean` +6, `filepathlite/PkgInit` +1, raxos SharedLoop +1; `Proof/sync/MutexLitSemantics.lean` gone).
  - **REGRESSION TO DECIDE:** three existing trust-boundary axioms, `runtime.opaqueInitsOk`, `runtime.initFuncsOk`, `internal.runtime.sys.opaqueInitsOk` (`Proof/runtime/Init.lean`, `Proof/internal/runtime/sys/Init.lean`: runtime's untranslated initializers and `init` functions return), used by 11 roots before and **81** after: every result whose program imports `os` or `net` now runs `runtime`'s initializer, because the translated Go `os` imports `runtime` (`runtime.KeepAlive` in `File.Fd`/`readFrom`/..., `runtime.Cleanup` in `Process`). 30 top-level results gain them, among them the net examples' `*_crash_robust`, `counter/paxos/rabia/quepaxa/epaxos_remote_robust`, `osfs_*` `crash_robust`, `raft_kvnet_robust_example` (0 -> 3), the raft kv results (9 -> 12), `kv_porcupine_robust` (7 -> 10), `raft_tracecheck_robust` (10 -> 13), and **RaftNoAx's `raft_kvdurable_porcupine_robust` (0 -> 3), whose point is no axiom of this repository** (its collection `etc/tcb-collections/raft-noax.txt` would fail `--check`). Options: (a) prove runtime's initializer instead of assuming it (Perennial's runtime model of the basic slice may give `runtime.wp_initialize'`: check after it lands); (b) keep `runtime` out of etcd-grove os's imports (os.toml: `runtime.KeepAlive` and `Cleanup` are what pull it in; KeepAlive is a no-op in the model); (c) accept and update the baselines. Not decided here (rule: no new axioms in a result's trust base without your OK).
- `etc/model-tests.sh` (etcd-grove os, syscall, durable, net, crc32, go/token; with the fixes): `gomodels:
  tests ok`; Perennial's: pass, skips listed with reasons.
