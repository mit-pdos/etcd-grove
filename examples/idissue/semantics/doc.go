// Package semantics explains, by Go tests over etcd's real idutil.Generator,
// each decision of the request ids' issue record, a model-only GooseLang
// extension (GooseLang/Ext/IdIssue/Impl.lean, the extension
// "go.etcd.io/etcd/pkg/v3/idutil.issue") that the trusted model of
// (*Generator).Next (TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean) steps
// through: Next's Go body, then `assume` of the record's "Issue" of the id and
// the generator, which holds exactly when no other generator issued the id.
// The record is the place where the model assumes what etcd relies on and does
// not check: a member's generators, one per start, never issue one id.
//
// Each file is one decision: its doc comment says what the model does, the
// Lean names that encode it, the outcome it allows or excludes, and why; its
// test runs the real generator to show the outcome (NewGenerator takes the
// clock as an argument, so the tests choose it).
//
//	I1 issue_one_issuer_test.go    an id has one issuer       idIssueOk, idIssueNext, "Issue"
//	I2 crash_keeps_record_test.go  a crash keeps the record,  idIssueCrash, idIssue_semantics.crash
//	                               as the past's (D4b)        (crash rest: Crash.lean, idIssueCrashStart)
//	I3 per_machine_test.go         one record per machine     LocalState (GlobalState := Unit)
//	I4 (no file)                   any initial record         ExtSemantics's default initLocal
//	                                                          (no assumption: a theorem holds
//	                                                          from the empty record too)
//
// The rule (CLAUDE.md): every change to the trusted semantics adds or updates
// the file of the decision it changes, in the same commit.
package semantics
