/-
Trusted code for `k8s.io/klog/v2`, in namespace `k8s_io.klog.v2` like the generated package (`Code/k8s_io/klog/v2.toml`): its `init`
functions, which the models skip: each docstring says why that is unobservable to the
translated code (etcd-grove#32); and the output side of klog's printf path (klog-printf,
2026-11-23, etcd-grove#25), `(*loggingT).header` and `(*loggingT).output`, which the translated
`printfDepth` calls around its `fmt.Fprintf`. Each model is **never more defined than Go**: where it
returns, Go returns (or ends the process) after the same effects on what translated code can read;
where Go may panic, the model panics.
-/
module

public import Perennial.Golang.Defn
public import Perennial.Code.bytes
public import Code.k8s_io.klog.v2.internal.buffer

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace k8s_io.klog.v2

noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- `k8s.io/klog/v2`'s `init` (klog v2.140.0) at `klog_file.go:52`: `host = shortHostname(os.Hostname())` (an error leaves `"unknownhost"`). It cannot panic. No translated code reads what it writes (`host`). The model does nothing (etcd-grove#32; until 2026-11-22 the
trust-boundary axiom `initFuncsOk` said it returns). -/
def init.«0».impl : val :=
  λ: <>, #()

/-- `k8s.io/klog/v2`'s `init` (klog v2.140.0) at `klog.go:426`: the default `logging` thresholds, the `commandLine` flag set's flags (constant, distinct names: a duplicate would panic), and `newFlushDaemon` (built, not started). It cannot panic. Of what it writes, translated code reads only
`logging.verbosity` and `logging.filterLength` (`V`, translated since klog-leaves, 2026-11-23), to which
it writes 0 (`setVState(0, nil, false)`, `klog.go:434`), and `logging.skipHeaders` (read by the
`header` model below; klog-printf, 2026-11-23), to which it writes `false` (the flag's default,
`klog.go:446`): the zero value `logging` is allocated with already has them. (It writes nothing to
`logging.logger` or `logging.filter`, which the printf path also reads.) The model does nothing (etcd-grove#32; until 2026-11-22 the
trust-boundary axiom `initFuncsOk` said it returns). -/
def init.«1».impl : val :=
  λ: <>, #()

/-- `loggingT`'s type (the translation's `loggingT.ty`: this module is imported by the translation). -/
@[reducible] def model.loggingT : go.GoType := go.GoType.Named go!"k8s.io/klog/v2.loggingT" []

/-- `settings`'s type (the translation's `settings.ty`), which `loggingT` embeds. -/
@[reducible] def model.settings : go.GoType := go.GoType.Named go!"k8s.io/klog/v2.settings" []

/-- `logWriter`'s type (the translation's `logWriter.ty`). -/
@[reducible] def model.logWriter : go.GoType := go.GoType.Named go!"k8s.io/klog/v2.logWriter" []

/-- `(*loggingT).header(s, depth) (*buffer.Buffer, string, int)` (klog v2.140.0, `klog.go:676-694`;
`formatHeader`, `klog.go:696-704`; `buffer.FormatHeader`, `internal/buffer/buffer.go:117-154`):
Go takes the caller's file and line from `runtime.Caller(3 + depth)` (`"???"` and 1 when it fails),
gets a buffer from the pool (`buffer.GetBuffer`: a `*Buffer` `New` allocated or one `Put` back,
`Reset` to empty, owned by the caller alone), and, unless `-skip_headers` (`l.skipHeaders`), writes
the header `Lmmdd hh:mm:ss.uuuuuu threadid file:line] ` into it (from `time.Now()`, the pid, the file
and the line), and returns the buffer, the file and the line. It cannot panic: `FormatHeader`'s
indices are in `Tmp`'s 64 bytes (two-digit fields of a month, day, hour, minute and second, six
and seven digits of the microseconds and the pid, at most 20 digits of a non-negative `int` line at
`Tmp[1:]`, then `]` and a space), and the header is at most 30 + len(file) + 23 bytes.

**The model:** a fresh zero `*Buffer` (what the pool's `New` returns, `Reset`), into which, unless
`l.skipHeaders`, it writes `"] "` -- the last two bytes of every header Go writes (`buffer.go:151-153`)
-- and returns it with `"???"` and 1, what Go returns when `runtime.Caller` fails. **Why faithful:**
the translated callers (`printfDepth`) read of what `header` returns only the buffer's bytes (their
last, in `buf.Bytes()[buf.Len()-1]`) and pass it, the file and the line to `output` (whose model
reads none of them); the model's header is a suffix of Go's, so it is empty exactly when Go's is
(`-skip_headers`) and otherwise ends in the same byte, a space. A buffer from the pool is the
caller's alone, as the fresh one is. Both always return, as Go does. -/
noncomputable def loggingT.header.impl : val :=
  λ: "l" "s" "depth",
    let: "b" := GoAlloc k8s_io.klog.v2.internal.buffer.Buffer.ty
      (GoZeroVal k8s_io.klog.v2.internal.buffer.Buffer.ty #()) in
    (if: ![go.bool] (StructFieldRef model.settings go!"skipHeaders"
          (StructFieldRef model.loggingT go!"settings" "l")) then #()
     else
      App (App (Val (GoInstruction (MethodResolve (go.PointerType _root_.Perennial.bytes.Buffer.ty)
          go!"WriteByte"))) (StructFieldRef k8s_io.klog.v2.internal.buffer.Buffer.ty go!"Buffer" "b"))
        (Val #(W8 93)) ;;
      App (App (Val (GoInstruction (MethodResolve (go.PointerType _root_.Perennial.bytes.Buffer.ty)
          go!"WriteByte"))) (StructFieldRef k8s_io.klog.v2.internal.buffer.Buffer.ty go!"Buffer" "b"))
        (Val #(W8 32)) ;; #()) ;;
    (("b", #"???"), #(W64 1))

/-- `(*loggingT).output(s, logger, buf, depth, file, line, alsoToStderr)` (klog v2.140.0,
`klog.go:885-1010`): under `l.mu`, Go writes the buffer's bytes out -- to `logger` when one is set
(`logger != nil`: its `writeKlogBuffer`, or its `logr` sink's `Error`/`Info`, code of the installer's),
otherwise to standard error and/or klog's log files (`l.file[s]`, created on first use; a write
error ignored; a creation error ends the process, `l.exit`: `os.Exit(2)`) -- with a stack dump
first if `-log_backtrace_at` matches (`traceLocation`); a `FatalLog` (`s = 3`) then dumps all
stacks and ends the process (`OsExit`); otherwise it puts the buffer back to the pool
(`buffer.PutBuffer`), counts the line in `severityStats[s]` and returns. An `s` outside
`InfoLog..FatalLog` (0..3) indexes `l.file`/`severityStats` out of range: a panic.

**The model:** returns, doing nothing, when `logger` is `nil` and `s` is one of 0..3; panics
otherwise. **Why faithful:** with no logger and a valid severity Go runs no foreign code, and of
what it writes (klog's files, standard error, `severityStats`, the pool, `l.file`, its private
fields) no translated code reads anything; it returns, or ends the process (the model returning
instead only adds executions, so a result proved of the model's covers Go's up to the exit). With a
logger it runs the installer's code, and with another `s` it panics: the model panics there, less
defined than Go. -/
noncomputable def loggingT.output.impl : val :=
  λ: "l" "s" "logger" "buf" "depth" "file" "line" "alsoToStderr",
    if: ("logger" =⟨go.PointerType model.logWriter⟩ #null) &&
        (("s" =⟨go.int32⟩ #(W32 0)) || ("s" =⟨go.int32⟩ #(W32 1)) ||
         ("s" =⟨go.int32⟩ #(W32 2)) || ("s" =⟨go.int32⟩ #(W32 3))) then #()
    else Panic "klog: output with a logger, or of an invalid severity, not modelled"

end code
end

end k8s_io.klog.v2

end Perennial
