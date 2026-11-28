# Trust delta: range origin/goose-model-overlay-basic..HEAD

## Files by tier

### tier 0 (TRUSTED)
- [M] Perennial/Code/fmt.toml  (goose-config; +20 -10)
- [M] Perennial/Code/log.toml  (goose-config; +11 -4)
- [M] Perennial/Code/os.toml  (goose-config; +2 -1)
- [M] Perennial/Code/syscall.toml  (goose-config; +18 -12)
- [M] Perennial/TrustedCode/fmt.lean  (trusted-model; +54 -4053)
- [M] Perennial/TrustedCode/log.lean  (trusted-model; +4 -30)
- [M] Perennial/TrustedCode/os.lean  (trusted-model; +5 -4)
- [M] Perennial/TrustedCode/syscall.lean  (trusted-model; +7 -70)
- [D] goose/model/fmt/fprintf_alias_test.go  (translator; +0 -115)
- [A] goose/model/fmt/method_panic_test.go  (translator; +39 -0)
- [A] goose/model/fmt/model_copy_test.go  (translator; +49 -0)
- [M] goose/model/fmt/model_diff_test.go  (translator; +66 -8)
- [A] goose/model/fmt/model_harness_test.go  (translator; +135 -0)
- [M] goose/model/fmt/model_test.go  (translator; +62 -124)
- [M] goose/model/fmt/sprintf_test.go  (translator; +4 -27)
- [A] goose/model/fmt/testdata/alias/alias_goose_test.go  (translator; +7 -0)
- [A] goose/model/fmt/testdata/alias/alias_test.go  (translator; +108 -0)
- [A] goose/model/fmt/testdata/alias/gomodel_driven.go  (translator; +31 -0)
- [A] goose/model/overlay/fmt/print.go  (go-model-overlay; +152 -0)
- [A] goose/model/overlay/fmt/printmodel.go  (go-model-overlay; +691 -0)
- [A] goose/model/overlay/log/log.go  (go-model-overlay; +69 -0)
- [A] goose/model/overlay/syscall/prlimit.go  (go-model-overlay; +34 -0)
- [M] goose/util/model.go  (translator; +10 -57)
- [M] goose/util/model_test.go  (translator; +0 -71)

### tier 1 (generated)
- [M] Perennial/Code/fmt.lean  (generated-code; +3730 -64)
- [M] Perennial/Code/log.lean  (generated-code; +152 -1)
- [M] Perennial/Code/syscall.lean  (generated-code; +14 -0)
- [M] Perennial/Code/syscall/chunk0.lean  (generated-code; +233 -2)
- [M] Perennial/GeneratedProof/fmt.lean  (generated-proof; +2 -0)
- [M] Perennial/GeneratedProof/log.lean  (generated-proof; +25 -0)
- [M] Perennial/GeneratedProof/syscall.lean  (generated-proof; +2 -0)
- [M] Perennial/GeneratedProof/syscall/chunk1.lean  (generated-proof; +2 -0)
- [M] Perennial/GeneratedProof/syscall/chunk2.lean  (generated-proof; +2 -0)
- [M] Perennial/GeneratedProof/syscall/chunk3.lean  (generated-proof; +2 -0)
- [M] Perennial/GeneratedProof/syscall/chunk4.lean  (generated-proof; +2 -0)
- [M] Perennial/GeneratedProof/syscall/chunk5.lean  (generated-proof; +2 -0)
- [M] Perennial/GeneratedProof/syscall/chunk6.lean  (generated-proof; +2 -0)
- [M] Perennial/GeneratedProof/syscall/chunk7.lean  (generated-proof; +2 -0)

### tier 3 (proofs, docs, tooling)
- [M] .agents/skills/land/SKILL.md  (other; +6 -26)
- [D] .agents/skills/review-trusted/CRITERIA.md  (other; +0 -82)
- [M] .agents/skills/review-trusted/SKILL.md  (other; +11 -112)
- [M] AGENTS.md  (other; +3 -18)
- [M] Perennial/Proof/fmt.lean  (other; +5 -4)
- [M] Perennial/Proof/fmt/Base.lean  (other; +4 -2)
- [M] Perennial/Proof/fmt/BytesModel.lean  (other; +16 -190)
- [M] Perennial/Proof/fmt/BytesResults.lean  (other; +3 -44)
- [M] Perennial/Proof/fmt/DoPrintf.lean  (other; +112 -40)
- [M] Perennial/Proof/fmt/Errorf.lean  (other; +159 -11)
- [M] Perennial/Proof/fmt/Fprint.lean  (other; +75 -27)
- [M] Perennial/Proof/fmt/Fprintf.lean  (other; +34 -13)
- [A] Perennial/Proof/fmt/Fprintln.lean  (other; +129 -0)
- [M] Perennial/Proof/fmt/Link.lean  (other; +22 -16)
- [M] Perennial/Proof/fmt/PrintArgs.lean  (other; +30 -13)
- [M] Perennial/Proof/fmt/Printf.lean  (other; +37 -6)
- [M] Perennial/Proof/fmt/Results.lean  (other; +53 -5)
- [M] Perennial/Proof/fmt/SprintfModel.lean  (other; +113 -68)
- [M] Perennial/Proof/fmt/VisitModel.lean  (other; +112 -58)
- [M] Perennial/Proof/fmt/initialize.lean  (other; +12 -6)
- [M] Perennial/Proof/internal/poll/Base.lean  (other; +10 -3)
- [M] Perennial/Proof/internal/poll/initialize.lean  (other; +11 -1)
- [M] Perennial/Proof/log.lean  (other; +1 -1)
- [M] Perennial/Proof/log/Base.lean  (other; +2 -0)
- [M] Perennial/Proof/log/Link.lean  (other; +12 -2)
- [M] Perennial/Proof/log/Printf.lean  (other; +36 -3)
- [A] Perennial/Proof/log/Println.lean  (other; +65 -0)
- [M] Perennial/Proof/log/initialize.lean  (other; +10 -4)
- [A] Perennial/Proof/log/modelDiscard__Write.lean  (other; +37 -0)
- [M] Perennial/Proof/os/Models.lean  (other; +11 -6)
- [M] Perennial/Proof/strings/Base.lean  (other; +71 -1)
- [M] Perennial/Proof/syscall/Base.lean  (other; +3 -52)
- [M] Perennial/Proof/syscall/Link.lean  (other; +3 -1)
- [M] Perennial/Proof/syscall/initialize.lean  (other; +158 -7)
- [A] Perennial/Spec/fmt/Fprintln.lean  (other; +41 -0)
- [M] Perennial/Spec/log/Printf.lean  (other; +4 -4)
- [A] Perennial/Spec/log/Println.lean  (other; +38 -0)
- [A] Perennial/Spec/log/modelDiscard__Write.lean  (other; +35 -0)
- [M] README.md  (other; +1 -2)
- [M] etc/land.sh  (other; +10 -97)
- [D] etc/model-deviations.py  (other; +0 -66)
- [M] etc/model-tests.sh  (other; +71 -4)
- [M] etc/trusted-delta.py  (other; +20 -278)
- [M] go.mod  (other; +5 -5)
- [M] go.sum  (other; +8 -0)
- [M] go.work  (other; +1 -1)
- [M] goose/README.md  (other; +1 -2)
- [D] goose/model-overlays-plan.md  (other; +0 -189)

## Signals in changed lines

### Perennial/Code/fmt.toml  (tier 0, goose-config)
- `trusted-list` Perennial/Code/fmt.toml:11 (removed; old line): `"!errorf", "!Println",`
- `trusted-list` Perennial/Code/fmt.toml:13 (removed; old line): `"!Errorf", "!Fprint", "!Fprintf", "!Print", "!Printf",`
- `trusted-list` Perennial/Code/fmt.toml:15: `"!Print", "!Println", "!Printf",`
- `trusted-list` Perennial/Code/fmt.toml:17: `"!underlyingAs", "!kindIs",`
- `trusted-list` Perennial/Code/fmt.toml:21 (removed; old line): `trusted = ["Errorf", "Fprint", "Fprintf", "Print", "Printf"]`
- `trusted-list` Perennial/Code/fmt.toml:27: `trusted = ["underlyingAs", "kindIs", "Printf"]`
- `model-table` Perennial/Code/fmt.toml:32: `[model]`
- `model-replaces` Perennial/Code/fmt.toml:34: `replaces = ["errorf", "Fprintf", "pp.doPrint", "pp.doPrintln"]`

### Perennial/Code/log.toml  (tier 0, goose-config)
- `trusted-list` Perennial/Code/log.toml:5: `trusted = ["std"]`
- `trusted-list` Perennial/Code/log.toml:6 (removed; old line): `trusted = ["Printf", "Println", "std", "init.0"]`
- `model-table` Perennial/Code/log.toml:16: `[model]`
- `model-replaces` Perennial/Code/log.toml:18: `replaces = ["Printf", "Println", "init.0"]`

### Perennial/Code/syscall.toml  (tier 0, goose-config)
- `trusted-list` Perennial/Code/syscall.toml:23: `trusted = ["runtime_envs", "Exit"]`
- `trusted-list` Perennial/Code/syscall.toml:24 (removed; old line): `trusted = ["runtime_envs", "init.0", "Exit"]`
- `model-table` Perennial/Code/syscall.toml:33: `[model]`
- `model-replaces` Perennial/Code/syscall.toml:35: `replaces = ["prlimit1"]`

### Perennial/TrustedCode/fmt.lean  (tier 0, trusted-model)
- `set_option` Perennial/TrustedCode/fmt.lean:16: `set_option linter.iris.style.nameCheck false`
- `set_option` Perennial/TrustedCode/fmt.lean:32 (removed; old line): `set_option linter.iris.style.nameCheck false`
- `panic` Perennial/TrustedCode/fmt.lean:2152 (removed; old line): `(LamV BAnon (Panic "fmt: not modelled"))`
- `trusted-impl` Perennial/TrustedCode/fmt.lean:3732 (removed; old line): `noncomputable def Fprintf.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/fmt.lean:3840 (removed; old line): `noncomputable def Errorf.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/fmt.lean:4043 (removed; old line): `noncomputable def Fprint.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/fmt.lean:4107 (removed; old line): `def Print.impl : val :=`
- `panic` Perennial/TrustedCode/fmt.lean:4109 (removed; old line): `Panic "unimplemented"`

### Perennial/TrustedCode/log.lean  (tier 0, trusted-model)
- `trusted-impl` Perennial/TrustedCode/log.lean:18 (removed; old line): `def Printf.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/log.lean:21 (removed; old line): `def Println.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/log.lean:61 (removed; old line): `def init.«0».impl : val :=`

### Perennial/TrustedCode/syscall.lean  (tier 0, trusted-model)
- `trusted-impl` Perennial/TrustedCode/syscall.lean:89 (removed; old line): `def init.«0».impl : val :=`

### goose/model/fmt/model_copy_test.go  (tier 0, translator)
- `gomodel-choice` goose/model/fmt/model_copy_test.go:6: `// gomodel.ChooseUint64() replaced by arbitrary() and each gomodel.Choose() by arbitraryBool()`
- `gomodel-choice` goose/model/fmt/model_copy_test.go:22: `s = strings.ReplaceAll(s, "gomodel.ChooseUint64()", "arbitrary()")`
- `gomodel-choice` goose/model/fmt/model_copy_test.go:23: `s = strings.ReplaceAll(s, "gomodel.Choose()", "arbitraryBool()")`

### goose/model/fmt/model_harness_test.go  (tier 0, translator)
- `gomodel-choice` goose/model/fmt/model_harness_test.go:25: `// arbitraryChoice is what gomodel.ChooseUint64() returns (arbitrary(); the tests run each choice).`
- `gomodel-choice` goose/model/fmt/model_harness_test.go:30: `// arbitraryBool is what gomodel.Choose() returns: false, so that writeArbitrary appends one`
- `gomodel-choice` goose/model/fmt/model_harness_test.go:50: `// notModelled stands for gomodel.Stuck() (no behaviour): the tests see a panic.`

### goose/model/overlay/fmt/print.go  (tier 0, go-model-overlay)
- `gomodel-choice` goose/model/overlay/fmt/print.go:125: `for gomodel.ChooseUint64() != 0 {`
- `gomodel-choice` goose/model/overlay/fmt/print.go:126: `s += string([]byte{byte(gomodel.ChooseUint64())})`
- `gomodel-choice` goose/model/overlay/fmt/print.go:133: `gomodel.Stuck()`

### goose/model/overlay/fmt/printmodel.go  (tier 0, go-model-overlay)
- `gomodel-choice` goose/model/overlay/fmt/printmodel.go:600: `for gomodel.Choose() {`
- `gomodel-choice` goose/model/overlay/fmt/printmodel.go:667: `n := gomodel.ChooseUint64()`

### goose/model/overlay/log/log.go  (tier 0, go-model-overlay)
- `gomodel-choice` goose/model/overlay/log/log.go:40: `if gomodel.Choose() {`
- `gomodel-choice` goose/model/overlay/log/log.go:49: `if gomodel.Choose() {`
- `gomodel-replace` goose/model/overlay/log/log.go:67: `//gomodel:replace init.0 "internal.DefaultOutput = func(pc uintptr, data []byte) error {"`

### goose/model/overlay/syscall/prlimit.go  (tier 0, go-model-overlay)
- `gomodel-choice` goose/model/overlay/syscall/prlimit.go:25: `if old != nil && gomodel.Choose() {`
- `gomodel-choice` goose/model/overlay/syscall/prlimit.go:26: `old.Cur = gomodel.ChooseUint64()`
- `gomodel-choice` goose/model/overlay/syscall/prlimit.go:27: `old.Max = gomodel.ChooseUint64()`
- `gomodel-choice` goose/model/overlay/syscall/prlimit.go:29: `e1 := Errno(gomodel.ChooseUint64())`

### Perennial/Code/fmt.lean  (tier 1, generated-code)
- `trusted-impl` Perennial/Code/fmt.lean:450: `noncomputable def Errorf.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/fmt.lean:496: `noncomputable def errorf.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/fmt.lean:2433: `noncomputable def Fprintf.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/fmt.lean:2557: `noncomputable def Fprint.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/fmt.lean:4992: `noncomputable def printfFormat.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/fmt.lean:5018: `noncomputable def chooseString.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/fmt.lean:5042: `noncomputable def notModelled.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/fmt.lean:5050: `noncomputable def intVerb.impl [GooseExts] [GoGlobalContext] : val :=`
- `step-rule` Perennial/Code/fmt.lean:9116: `errorf_unfold : FuncUnfold errorf [] errorf.impl`
- `step-rule` Perennial/Code/fmt.lean:5531 (removed; old line): `Print_unfold : FuncUnfold Print [] Print.impl`
- `step-rule` Perennial/Code/fmt.lean:9134: `printfFormat_unfold : FuncUnfold printfFormat [] printfFormat.impl`
- `step-rule` Perennial/Code/fmt.lean:9135: `chooseString_unfold : FuncUnfold chooseString [] chooseString.impl`
- `step-rule` Perennial/Code/fmt.lean:9136: `notModelled_unfold : FuncUnfold notModelled [] notModelled.impl`
- `step-rule` Perennial/Code/fmt.lean:9137: `underlyingAs_unfold : ∀ (T : go.GoType), FuncUnfold underlyingAs [T] (underlyingAs.impl T)`
- `step-rule` Perennial/Code/fmt.lean:9138: `kindIs_unfold : ∀ (T : go.GoType), FuncUnfold kindIs [T] (kindIs.impl T)`
- `step-rule` Perennial/Code/fmt.lean:9139: `intVerb_unfold : FuncUnfold intVerb [] intVerb.impl`
- `trusted-impl`: ... and 29 more lines in this file
- `step-rule`: ... and 29 more lines in this file

### Perennial/Code/log.lean  (tier 1, generated-code)
- `trusted-impl` Perennial/Code/log.lean:142: `noncomputable def init.«0».impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/log.lean:178: `noncomputable def Printf.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/log.lean:199: `noncomputable def Println.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/log.lean:213: `noncomputable def modelDiscard.Write.impl [GooseExts] [GoGlobalContext] : val :=`
- `step-rule` Perennial/Code/log.lean:317: `Write_unfold : MethodUnfold modelDiscard.ty go!"Write" modelDiscard.Write.impl`
- `step-rule` Perennial/Code/log.lean:318: `ptr_Write_unfold : MethodUnfold (go.GoType.PointerType modelDiscard.ty) go!"Write" (LamV "$r"`

### Perennial/Code/syscall.lean  (tier 1, generated-code)
- `step-rule` Perennial/Code/syscall.lean:109: `adjustFileLimit_unfold : FuncUnfold adjustFileLimit [] adjustFileLimit.impl`
- `step-rule` Perennial/Code/syscall.lean:111: `Getrlimit_unfold : FuncUnfold Getrlimit [] Getrlimit.impl`
- `step-rule` Perennial/Code/syscall.lean:112: `setrlimit_unfold : FuncUnfold setrlimit [] setrlimit.impl`
- `step-rule` Perennial/Code/syscall.lean:113: `errnoErr_unfold : FuncUnfold errnoErr [] errnoErr.impl`
- `step-rule` Perennial/Code/syscall.lean:114: `prlimit1_unfold : FuncUnfold prlimit1 [] prlimit1.impl`

### Perennial/Code/syscall/chunk0.lean  (tier 1, generated-code)
- `opaque` Perennial/Code/syscall/chunk0.lean:2077 (removed; old line): `opaque RLIMIT_NOFILE [GooseExts] [GoGlobalContext] : val`
- `trusted-impl` Perennial/Code/syscall/chunk0.lean:5433: `noncomputable def init.«0».impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/syscall/chunk0.lean:5473: `noncomputable def adjustFileLimit.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/syscall/chunk0.lean:5482: `noncomputable def Getrlimit.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/syscall/chunk0.lean:5506: `noncomputable def setrlimit.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/syscall/chunk0.lean:5530: `noncomputable def errnoErr.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/syscall/chunk0.lean:5589: `noncomputable def prlimit1.impl [GooseExts] [GoGlobalContext] : val :=`

### Perennial/GeneratedProof/log.lean  (tier 1, generated-proof)
- `extension` Perennial/GeneratedProof/log.lean:45: `variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]`

### Perennial/Proof/fmt/BytesModel.lean  (tier 3, other)
- `set_option` Perennial/Proof/fmt/BytesModel.lean:757 (removed; old line): `set_option maxHeartbeats 2000000 in`
- `set_option` Perennial/Proof/fmt/BytesModel.lean:788 (removed; old line): `set_option maxHeartbeats 2000000 in`
- `set_option` Perennial/Proof/fmt/BytesModel.lean:830 (removed; old line): `set_option maxHeartbeats 2000000 in`
- `set_option` Perennial/Proof/fmt/BytesModel.lean:856 (removed; old line): `set_option maxHeartbeats 2000000 in`

### Perennial/Proof/fmt/Fprintln.lean  (tier 3, other)
- `extension` Perennial/Proof/fmt/Fprintln.lean:24: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/log/Println.lean  (tier 3, other)
- `extension` Perennial/Proof/log/Println.lean:21: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/log/modelDiscard__Write.lean  (tier 3, other)
- `set_option` Perennial/Proof/log/modelDiscard__Write.lean:10: `set_option linter.iris.style.nameCheck false`
- `extension` Perennial/Proof/log/modelDiscard__Write.lean:19: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/syscall/Base.lean  (tier 3, other)
- `extension` Perennial/Proof/syscall/Base.lean:40 (removed; old line): `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/fmt/Fprintln.lean  (tier 3, other)
- `extension` Perennial/Spec/fmt/Fprintln.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/log/Println.lean  (tier 3, other)
- `extension` Perennial/Spec/log/Println.lean:18: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/log/modelDiscard__Write.lean  (tier 3, other)
- `set_option` Perennial/Spec/log/modelDiscard__Write.lean:10: `set_option linter.iris.style.nameCheck false`
- `extension` Perennial/Spec/log/modelDiscard__Write.lean:19: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### etc/trusted-delta.py  (tier 3, other)
- `assume` etc/trusted-delta.py:846 (removed; old line): `"assume",           # a model assumption: removes executions`
- `assume` etc/trusted-delta.py:860 (removed; old line): `NOT_NARROWING = {"assume", "angelic", "axiom", "new-instruction", "model-table"}`
- `angelic` etc/trusted-delta.py:1211 (removed; old line): `if new_instruction_hits(instr, [2, 4, 5, 6, 7, 8]) != [(4, "| AngelicExit"), (6, "| AsAssign"),`
- `step-rule` etc/trusted-delta.py:1214 (removed; old line): `rule = [("Perennial/Golang/Defn/X.lean", 3, "step-rule", "⟦GoUnOp GoPos t, #v⟧ ⤳ #v")]`
- `assume` etc/trusted-delta.py:1215 (removed; old line): `assume = rule + [("Perennial/GooseLang/Lang.lean", 9, "assume", "assume (n < 2^63)")]`
- `assume` etc/trusted-delta.py:1233 (removed; old line): `(assume, ["none (narrowing: tighter)"], [], False),`
- `assume` etc/trusted-delta.py:1234 (removed; old line): `(assume, ["goose/testdata/examples/semantics/plus.go"], real, True),`
- `assume` etc/trusted-delta.py:1236 (removed; old line): `(assume, ["none (narrowing: x)", "goose/testdata/examples/semantics/missing.go",`

Signal legend:
- `axiom`: a new axiom: trusted outright
- `sorry`: an unproved obligation; in tiers 0-2 it is an axiom
- `opaque`: an opaque constant: a value nobody can inspect
- `native`: trusts native code (forbidden by README)
- `implemented_by`: runtime behaviour differs from the definition
- `unsafe`: Lean unsafe definition
- `partial`: partial def: an opaque constant in disguise
- `assume`: a model assumption: must be unreachable in Go (README, Model assumptions)
- `angelic`: an angelic exit: the model refuses to continue (sound only if Go cannot reach it)
- `panic`: a (stuck) run-time panic in the model
- `step-rule`: a semantics rule or unfolding (any form: `⤳`, `is_go_step_pure`, `IsGoStepPureDet`, `FuncUnfold`, ...; in tier 0 also a changed line inside one)
- `semantics-class`: a semantics class, or an instance of one (or of the contexts defining `is_go_step_pure`)
- `adequacy`: an adequacy theorem or its parameters
- `trusted-impl`: a hand-written model of Go code
- `trusted-list`: goose configuration: what is trusted/translated/axiomatized
- `skip-list`: goose configuration: package variables not translated at all (trusted: not running each initializer is unobservable)
- `global-var-addr`: the address of a package variable by its literal name: the one way hand-written code can reach a variable goose skips (the name has no Lean declaration)
- `extension`: an extension's semantics (new primitive operations)
- `set_option`: an option change (linters off, max heartbeats, ...)
- `verbatim`: goose emits Lean text verbatim
- `model-table`: goose configuration: a Go model overlay (model Go replaces or adds to the real package; R12)
- `model-replaces`: goose configuration: which real declarations a Go model replaces, or which methods it may add to real types (R12)
- `gomodel-replace`: a Go model `init` that replaces a real `init.N` (R12)
- `gomodel-choice`: a choice or stuck point in a Go model: needs a reason (review-trusted)

## goose configuration (trusted / translated / axiomatized / skipped)

- Perennial/Code/fmt.toml `imports`: added ['internal/stringslite', 'internal/gomodel'], removed []
- Perennial/Code/fmt.toml `translate`: added ['!underlyingAs', '!kindIs'], removed ['!errorf', '!Errorf', '!Fprint', '!Fprintf']
- Perennial/Code/fmt.toml `trusted`: added ['underlyingAs', 'kindIs'], removed ['Errorf', 'Fprint', 'Fprintf', 'Print']
  - R2: `underlyingAs` must be justified by a goose run on the real source that fails on something irreducible (not a missing goose feature or semantics rule): move it to `translate` in a copy of the configuration and run `goose -configdir <copy> -dir goose fmt` (SKILL.md, step 4)
  - R2: `kindIs` must be justified by a goose run on the real source that fails on something irreducible (not a missing goose feature or semantics rule): move it to `translate` in a copy of the configuration and run `goose -configdir <copy> -dir goose fmt` (SKILL.md, step 4)
- Perennial/Code/log.toml `imports`: added ['fmt', 'internal/gomodel'], removed []
- Perennial/Code/log.toml `trusted`: added [], removed ['Printf', 'Println', 'init.0']
- Perennial/Code/syscall.toml `imports`: added ['sync/atomic', 'internal/gomodel'], removed []
- Perennial/Code/syscall.toml `translate`: added ['init.0', 'origRlimitNofile', 'Getrlimit', 'setrlimit', 'adjustFileLimit', 'errnoErr', 'RLIMIT_NOFILE'], removed []
- Perennial/Code/syscall.toml `trusted`: added [], removed ['init.0']

A declaration that is neither translated nor trusted is axiomatized (name and type only). A `!pattern` in `translate` with the same name in `trusted` replaces goose's translation by a hand-written model: ask why the real translation is not used.

## Go model overlays (TRUSTED: model Go is reviewed as Go, rule R12)

For each replaced declaration: every behaviour of the real one (gc, linux/amd64, the pinned Go), under every use by the program and the real package, must be a behaviour of the model's translation. Compare the two sources line by line; every `gomodel.Choose`/`ChooseUint64`/`Stuck` needs a reason in the doc comment.

### Perennial/Code/fmt.toml  (package `fmt`)

- `[model]` before: none
- `[model]` after:  dir = 'goose/model/overlay/fmt', replaces = ['errorf', 'Fprintf', 'pp.doPrint', 'pp.doPrintln'], added_methods = []
- model files: goose/model/overlay/fmt/print.go, goose/model/overlay/fmt/printmodel.go; changed: goose/model/overlay/fmt/print.go, goose/model/overlay/fmt/printmodel.go

#### `fmt.Fprintf` (new)

Model (goose/model/overlay/fmt/print.go:63):

```go
// MODEL: Fprintf is Go's, but for one line: Go's p.doPrintf(format, a) is the model printer's
// doPrintf(&p.buf, format, a, false), which appends to p.buf what Go appends up to its first
// method call or directive the model does not format, and arbitrary strings from there, before
// each method call and at the end (see the file comment for what the model printer covers and
// where it is stuck; TestModelFprintf checks the bytes Write receives and the methods called;
// TestModelAlias a method reading p.buf through a slice an earlier Write kept). The printer, its
// pool (ppFree), the one w.Write(p.buf) and p.free() are Go's own.
func Fprintf(w io.Writer, format string, a ...any) (n int, err error) {
	p := newPrinter()
	doPrintf(&p.buf, format, a, false)
	n, err = w.Write(p.buf)
	p.free()
	return
}
```

Real (`go doc -u -src fmt.Fprintf`):

```go
package fmt // import "fmt"

// Fprintf formats according to a format specifier and writes to w.
// It returns the number of bytes written and any write error encountered.
func Fprintf(w io.Writer, format string, a ...any) (n int, err error) {
	p := newPrinter()
	p.doPrintf(format, a)
	n, err = w.Write(p.buf)
	p.free()
	return
}
```

#### `fmt.errorf` (new)

Model (goose/model/overlay/fmt/print.go:40):

```go
// MODEL: errorf is Go's, but for its printer: Go's p.doPrintf(format, a), with p.wrapErrs set, is
// the model printer's doPrintf(&p.buf, format, a, true), which appends the message to p.buf (Go's,
// with arbitrary strings from the first directive it does not format) and gives the indices of the
// %w arguments (or that they are unknown); errorfResult builds the error from them as Go's switch
// on len(p.wrappedErrs) does: errors.New, a *wrapError, a *wrapErrors (see the file comment for
// what the model printer covers and where it is stuck; TestModelErrorf compares the error's kind,
// message and wrapped errors with Go's). The printer is Go's own, from newPrinter and back to the
// pool with p.free(), and the message is read back from p.buf as Go reads it: the pool is
// observable outside fmt, since Fprintf hands p.buf to a writer, which may keep the slice and see
// what a later errorf writes into the same printer's buffer, or write into it itself
// (TestModelAlias, goose/model/fmt).
func errorf(format string, a ...any) error {
	if len(a) == 0 && stringslite.IndexByte(format, '%') == -1 {
		return nil
	}
	p := newPrinter()
	wrapped, unknown := doPrintf(&p.buf, format, a, true)
	s := string(p.buf)
	err := errorfResult(s, wrapped, unknown, a)
	p.free()
	return err
}
```

Real (`go doc -u -src fmt.errorf`):

```go
package fmt // import "fmt"

// Errorf formats according to a format specifier and returns the string as a
// value that satisfies error.
//
// If the format specifier includes a %w verb with an error operand,
// the returned error will implement an Unwrap method returning the operand.
// If there is more than one %w verb, the returned error will implement an
// Unwrap method returning a []error containing all the %w operands in the
// order they appear in the arguments.
// It is invalid to supply the %w verb with an operand that does not implement
// the error interface. The %w verb is otherwise a synonym for %v.
func Errorf(format string, a ...any) (err error) {
	// This function has been split in a somewhat unnatural way
	// so that both it and the errors.New call can be inlined.
	if err = errorf(format, a...); err != nil {
		return err
	}
	// No formatting was needed. We can avoid some allocations and other work.
	// See https://go.dev/cl/708836 for details.
	return errors.New(format)
}
// errorf formats and returns an error value, or nil if no formatting is required.
func errorf(format string, a ...any) error {
	if len(a) == 0 && stringslite.IndexByte(format, '%') == -1 {
		return nil
	}
	p := newPrinter()
	p.wrapErrs = true
	p.doPrintf(format, a)
	s := string(p.buf)
	var err error
	switch len(p.wrappedErrs) {
	case 0:
		err = errors.New(s)
	case 1:
		w := &wrapError{msg: s}
		w.err, _ = a[p.wrappedErrs[0]].(error)
		err = w
	default:
		if p.reordered {
			slices.Sort(p.wrappedErrs)
		}
		var errs []error
		for i, argNum := range p.wrappedErrs {
			if i > 0 && p.wrappedErrs[i-1] == argNum {
				continue
			}
			if e, ok := a[argNum].(error); ok {
				errs = append(errs, e)
			}
		}
		err = &wrapErrors{s, errs}
	}
	p.free()
	return err
}
```

#### `fmt.pp.doPrint` (new)

Model (goose/model/overlay/fmt/print.go:90):

```go
// MODEL: pp.doPrint prints the operands under %v, a space between two that are not strings. Go
// tells a string by reflect.TypeOf(arg).Kind() == reflect.String (reflection, which is stuck) and
// prints each with p.printArg, which is stuck on the operands of the file comment; Fprint's spec
// admits them (fmt.printArgOk). The model calls of each operand what Go's printArg calls under %v
// (visitArg: its Error() or String(), stuck where the model printer is), after appending arbitrary
// strings to p.buf (writeArbitrary), which stand for what Go has appended by then (a method may
// read p.buf through a slice a writer kept), and appends arbitrary strings at the end, for the
// rest of Go's output (TestModelFprint checks the calls, TestModelAlias the buffer). Fprint and
// Sprint, Go's own, print with it.
func (p *pp) doPrint(a []any) {
	for _, x := range a {
		writeArbitrary(&p.buf)
		visitArg(x, 'v', false, false)
	}
	writeArbitrary(&p.buf)
}
```

Real (`go doc -u -src fmt.pp.doPrint`):

```go
package fmt // import "fmt"

func (p *pp) doPrint(a []any) {
	prevString := false
	for argNum, arg := range a {
		isString := arg != nil && reflect.TypeOf(arg).Kind() == reflect.String
		// Add a space between two non-string arguments.
		if argNum > 0 && !isString && !prevString {
			p.buf.writeByte(' ')
		}
		p.printArg(arg, 'v')
		prevString = isString
	}
}
```

#### `fmt.pp.doPrintln` (new)

Model (goose/model/overlay/fmt/print.go:107):

```go
// MODEL: pp.doPrintln is doPrint's model (see there): Go's doPrintln, for each operand, appends a
// space if it is not the first and prints it with p.printArg(arg, 'v'), then appends '\n'; the
// model calls of each operand what printArg calls under %v (visitArg), after arbitrary strings
// (writeArbitrary), which cover Go's space and what printArg appended before, and ends with
// arbitrary strings, which cover the rest and the newline (TestModelFprintln checks the calls).
// Fprintln and Sprintln, Go's own, print with it.
func (p *pp) doPrintln(a []any) {
	for _, x := range a {
		writeArbitrary(&p.buf)
		visitArg(x, 'v', false, false)
	}
	writeArbitrary(&p.buf)
}
```

Real (`go doc -u -src fmt.pp.doPrintln`):

```go
package fmt // import "fmt"

// doPrintln is like doPrint but always adds a space between arguments
// and a newline after the last argument.
func (p *pp) doPrintln(a []any) {
	for argNum, arg := range a {
		if argNum > 0 {
			p.buf.writeByte(' ')
		}
		p.printArg(arg, 'v')
	}
	p.buf.writeByte('\n')
}
```

Additions (no claim of their own; a primitive stub carries the TrustedCode claim, R2; an added method must match `added_methods`):

- `printfFormat` (func, goose/model/overlay/fmt/print.go:78, new)
- `chooseString` (func, goose/model/overlay/fmt/print.go:121, new)
- `notModelled` (func, goose/model/overlay/fmt/print.go:131, new)
- `underlyingAs` (func, goose/model/overlay/fmt/print.go:136, new); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)
- `kindIs` (func, goose/model/overlay/fmt/printmodel.go:15, new); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)
- `intVerb` (func, goose/model/overlay/fmt/printmodel.go:26, new)
- `intArg` (func, goose/model/overlay/fmt/printmodel.go:44, new)
- `namedIntArg` (func, goose/model/overlay/fmt/printmodel.go:75, new)
- `anyIntArg` (func, goose/model/overlay/fmt/printmodel.go:115, new)
- `formatInt` (func, goose/model/overlay/fmt/printmodel.go:123, new)
- `formatHex` (func, goose/model/overlay/fmt/printmodel.go:144, new)
- `strArg` (func, goose/model/overlay/fmt/printmodel.go:165, new)
- `formatArg` (func, goose/model/overlay/fmt/printmodel.go:178, new)
- `hexNibble` (func, goose/model/overlay/fmt/printmodel.go:206, new)
- `quoteByte` (func, goose/model/overlay/fmt/printmodel.go:217, new)
- `quoteBytes` (func, goose/model/overlay/fmt/printmodel.go:251, new)
- `decBytes` (func, goose/model/overlay/fmt/printmodel.go:266, new)
- `hexBytes` (func, goose/model/overlay/fmt/printmodel.go:279, new)
- `joinStrings` (func, goose/model/overlay/fmt/printmodel.go:288, new)
- `formatSlice` (func, goose/model/overlay/fmt/printmodel.go:301, new)
- `isBasic` (func, goose/model/overlay/fmt/printmodel.go:344, new)
- `isIntKind` (func, goose/model/overlay/fmt/printmodel.go:357, new)
- `isStrKind` (func, goose/model/overlay/fmt/printmodel.go:365, new)
- `hasFmtMethod` (func, goose/model/overlay/fmt/printmodel.go:370, new)
- `inert` (func, goose/model/overlay/fmt/printmodel.go:388, new)
- `allInert` (func, goose/model/overlay/fmt/printmodel.go:407, new)
- `parseDirective` (func, goose/model/overlay/fmt/printmodel.go:417, new)
- `visitKind` (func, goose/model/overlay/fmt/printmodel.go:466, new)
- `callError` (func, goose/model/overlay/fmt/printmodel.go:478, new)
- `callString` (func, goose/model/overlay/fmt/printmodel.go:492, new)
- `visitArg` (func, goose/model/overlay/fmt/printmodel.go:502, new)
- `visitRest` (func, goose/model/overlay/fmt/printmodel.go:550, new)
- `writeArbitrary` (func, goose/model/overlay/fmt/printmodel.go:594, new)
- `doPrintf` (func, goose/model/overlay/fmt/printmodel.go:605, new)
- `errorfResult` (func, goose/model/overlay/fmt/printmodel.go:658, new)

### Perennial/Code/log.toml  (package `log`)

- `[model]` before: none
- `[model]` after:  dir = 'goose/model/overlay/log', replaces = ['Printf', 'Println', 'init.0'], added_methods = []
- model files: goose/model/overlay/log/log.go; changed: goose/model/overlay/log/log.go

#### `log.Printf` (new)

Model (goose/model/overlay/log/log.go:12):

```go
// MODEL: Printf is std.output(0, 2, func(b []byte) []byte { return
// fmt.Appendf(b, format, v...) }). The standard logger std is not translated
// (its initializer is New(os.Stderr, "", LstdFlags), and os.Stderr is not a
// File in the model: perennial#663), nor is any function that changes it
// (SetOutput, SetFlags, SetPrefix, Default, Logger's setters), so in every
// execution of the model std is as New made it: flags LstdFlags, no prefix,
// output os.Stderr. Its output method then:
//   - returns at once if the output is io.Discard (l.isDiscard), which needs
//     a SetOutput no execution reaches; the model has both outcomes anyway
//     (gomodel.Choose: it formats or does nothing);
//   - reads the clock (time.Now), the prefix and the flags (atomic loads), and
//     with LstdFlags not the caller's file and line: no effect;
//   - takes a buffer from bufferPool, formats the date and time into it, and
//     calls the closure, which formats the arguments as fmt.Appendf does:
//     fmt's printer and doPrintf, which call the arguments' Error, String and
//     Format methods, the only effects on the program. The model formats them
//     with fmt.Fprintf, which runs the same newPrinter, doPrintf and free;
//   - appends a newline, takes std.outMu (held only by output, never while
//     the arguments' methods run) and writes the bytes to standard error,
//     ignoring the result: an effect outside the program, which the model
//     drops, as it drops Fprintf's bytes (modelDiscard). The write can also
//     block (a full stderr pipe, holding std.outMu) or end the process
//     (EPIPE on fd 2: os.File.Write's epipecheck raises SIGPIPE): both stop
//     the program there, so their traces are prefixes of the model's, which
//     returns (partial correctness, as for an exit).
//
// Neither can panic other than through the arguments' methods.
func Printf(format string, v ...any) {
	if gomodel.Choose() {
		fmt.Fprintf(modelDiscard{}, format, v...)
	}
}
```

Real (`go doc -u -src log.Printf`):

```go
package log // import "log"

// Printf calls Output to print to the standard logger.
// Arguments are handled in the manner of [fmt.Printf].
func Printf(format string, v ...any) {
	std.output(0, 2, func(b []byte) []byte {
		return fmt.Appendf(b, format, v...)
	})
}
```

#### `log.Println` (new)

Model (goose/model/overlay/log/log.go:45):

```go
// MODEL: Println is Printf's model (see there) with fmt.Appendln(b, v...) in
// place of Appendf: the model formats the arguments with fmt.Fprintln, which
// runs the same newPrinter, doPrintln and free.
func Println(v ...any) {
	if gomodel.Choose() {
		fmt.Fprintln(modelDiscard{}, v...)
	}
}
```

Real (`go doc -u -src log.Println`):

```go
package log // import "log"

// Println calls Output to print to the standard logger.
// Arguments are handled in the manner of [fmt.Println].
func Println(v ...any) {
	std.output(0, 2, func(b []byte) []byte {
		return fmt.Appendln(b, v...)
	})
}
```

#### `log.init.0` (new)

Model (goose/model/overlay/log/log.go:62):

```go
// MODEL: log's init function stores a closure into
// log/internal.DefaultOutput, the output of log/slog's default handler; it
// cannot panic. log/slog and log/internal are not translated, so no execution
// of the model reads that variable, and the model does nothing.
//
//gomodel:replace init.0 "internal.DefaultOutput = func(pc uintptr, data []byte) error {"
func init() {
}
```

(`go doc` cannot show `init.0`, the real package's init of that number in goose's numbering: read it in the real source. The marker quotes its first body line: "internal.DefaultOutput = func(pc uintptr, data []byte) error {")

Additions (no claim of their own; a primitive stub carries the TrustedCode claim, R2; an added method must match `added_methods`):

- `modelDiscard` (type, goose/model/overlay/log/log.go:54, new)
- `modelDiscard.Write` (method, goose/model/overlay/log/log.go:58, new); a method: of a model-only type, or a config error

### Perennial/Code/syscall.toml  (package `syscall`)

- `[model]` before: none
- `[model]` after:  dir = 'goose/model/overlay/syscall', replaces = ['prlimit1'], added_methods = []
- model files: goose/model/overlay/syscall/prlimit.go; changed: goose/model/overlay/syscall/prlimit.go

#### `syscall.prlimit1` (new)

Model (goose/model/overlay/syscall/prlimit.go:9):

```go
// MODEL: prlimit1 is the prlimit64 system call: Go's body is
// RawSyscall6(SYS_PRLIMIT64, uintptr(pid), uintptr(resource),
// uintptr(unsafe.Pointer(newlimit)), uintptr(unsafe.Pointer(old)), 0, 0) and,
// for a non-zero errno, errnoErr(e1). The conversions of pointers to uintptr
// and the system call (assembly) have no semantics. The kernel reads
// *newlimit if newlimit is non-nil, writes *old if old is non-nil and the call
// succeeds, and returns 0 or an errno; it cannot fault on Go's pointers and
// cannot panic. The model reads *newlimit (so a concurrent write races, as
// with the kernel's read), may write arbitrary limits to *old (a superset of
// the kernel's writes: always on success, never on failure), and returns
// errnoErr of an arbitrary errno, nil for 0, as Go's stub does with the
// kernel's. The limits themselves, the process's state, are not modelled.
func prlimit1(pid int, resource int, newlimit *Rlimit, old *Rlimit) (err error) {
	if newlimit != nil {
		_ = *newlimit
	}
	if old != nil && gomodel.Choose() {
		old.Cur = gomodel.ChooseUint64()
		old.Max = gomodel.ChooseUint64()
	}
	e1 := Errno(gomodel.ChooseUint64())
	if e1 != 0 {
		err = errnoErr(e1)
	}
	return
}
```

Real (`go doc -u -src syscall.prlimit1`):

```go
package syscall // import "syscall"

func prlimit1(pid int, resource int, newlimit *Rlimit, old *Rlimit) (err error) {
	_, _, e1 := RawSyscall6(SYS_PRLIMIT64, uintptr(pid), uintptr(resource), uintptr(unsafe.Pointer(newlimit)), uintptr(unsafe.Pointer(old)), 0, 0)
	if e1 != 0 {
		err = errnoErr(e1)
	}
	return
}
```

## Trusted models vs the Go source

### Perennial/TrustedCode/fmt.lean: `underlyingAs.impl`

(the docstring quotes no Go code: the model must be read as GooseLang)

(`go doc -src fmt.underlyingAs` found nothing: fetch the source yourself)

### Perennial/TrustedCode/fmt.lean: `kindIs.impl`

(the docstring quotes no Go code: the model must be read as GooseLang)

(`go doc -src fmt.kindIs` found nothing: fetch the source yourself)

## Diffs

### Perennial/Code/fmt.toml  (tier 0, goose-config)

```diff
diff --git a/Perennial/Code/fmt.toml b/Perennial/Code/fmt.toml
index 166e74b52..a391af4db 100644
--- a/Perennial/Code/fmt.toml
+++ b/Perennial/Code/fmt.toml
@@ -1,24 +1,34 @@
-# The print path of print.go and format.go (`Sprintf` and the printer it runs), the package
-# variables, and errors.go's types. Not translated (stuck when called):
+# The print path of print.go and format.go (`Sprintf`, `Fprint`, `Errorf` and the printer they run),
+# the package variables, and errors.go's types. Not translated (stuck when called):
 # - `pp.printValue`, which formats by reflection (`reflect` has no semantics), and
 #   `pp.fmtComplex`, which needs the `real`/`imag` built-ins goose does not support;
 # - scan.go (only its package variables are translated, for the initializer);
-# - `errorf`, translated with `Errorf` at stage 2 of perennial#671, and `Println`, which writes
-#   to `os.Stdout`, with `Printf` and `Print` at stage 2.
+# - `Print` and `Println`, which write to `os.Stdout` (the model of os has none).
+# Go models (goose/model/overlay/fmt, [model] below): `errorf`, `Fprintf`, `pp.doPrint` and `pp.doPrintln` print
+# with the model printer (printmodel.go) where the real print path is stuck. `Printf` is trusted
+# (TrustedCode/fmt.lean, as on lean): it formats with the model's `printfFormat` and returns an
+# arbitrary count and error for the write to `os.Stdout` (translating the write needs a semantics
+# primitive for an arbitrary interface value, its error).
 translate = [
   "*",
   "!pp.printValue", "!pp.fmtComplex",
-  "!errorf", "!Println",
-  # trusted (below)
-  "!Errorf", "!Fprint", "!Fprintf", "!Print", "!Printf",
+  "!Print", "!Println", "!Printf",
+  # the primitive stubs (trusted, below)
+  "!underlyingAs", "!kindIs",
   # scan.go: only the package variables
   "!Scan", "!Scanln", "!Scanf", "!Sscan", "!Sscanln", "!Sscanf", "!Fscan", "!Fscanln", "!Fscanf",
   "!isSpace", "!notSpace", "!newScanState", "!indexRune", "!hasX", "!hexDigit", "!errorHandler",
   "!ss.*", "!readRune.*", "!stringReader.*", "!scanError.*",
 ]
-imports = ["!*", "io", "errors", "sync", "unicode/utf8", "reflect", "strconv"]
-# the trusted models of TrustedCode/fmt.lean, until stage 2 of perennial#671
-trusted = ["Errorf", "Fprint", "Fprintf", "Print", "Printf"]
+imports = ["!*", "io", "errors", "sync", "unicode/utf8", "reflect", "strconv", "internal/stringslite",
+  "internal/gomodel"]
+# the model's primitive stubs `underlyingAs` (goose/model/overlay/fmt/print.go) and `kindIs`
+# (printmodel.go), and `Printf`, modelled in TrustedCode/fmt.lean
+trusted = ["underlyingAs", "kindIs", "Printf"]
 
 # translate the definitions of all type declarations goose supports
 translate_types = true
+
+[model]
+dir = "goose/model/overlay/fmt"
+replaces = ["errorf", "Fprintf", "pp.doPrint", "pp.doPrintln"]
```

### Perennial/Code/log.toml  (tier 0, goose-config)

```diff
diff --git a/Perennial/Code/log.toml b/Perennial/Code/log.toml
index 9221763ec..123e1c058 100644
--- a/Perennial/Code/log.toml
+++ b/Perennial/Code/log.toml
@@ -1,11 +1,18 @@
 
 translate = ["Ldate", "Ltime", "LstdFlags", "bufferPool"]
 
-# `std` needs `os.Stderr` and `init.0` writes `log/internal`'s variable
-# (TrustedCode/log.lean)
-trusted = ["Printf", "Println", "std", "init.0"]
+# `std` needs `os.Stderr` (TrustedCode/log.lean)
+trusted = ["std"]
 
-imports = ["!*", "sync"]
+imports = ["!*", "sync", "fmt", "internal/gomodel"]
 
 # translate the definitions of all type declarations goose supports
 translate_types = true
+
+# The Go model (goose/model/overlay/log): each declaration's MODEL: comment says why it has at least
+# Go's behaviours. `Printf` and `Println` (`std.output`, over the untranslated `std`): fmt's
+# formatting of the arguments, or nothing; `init.0` (it writes `log/internal`'s variable, read only
+# by the untranslated `log/slog`): nothing.
+[model]
+dir = "goose/model/overlay/log"
+replaces = ["Printf", "Println", "init.0"]
```

### Perennial/Code/os.toml  (tier 0, goose-config)

```diff
diff --git a/Perennial/Code/os.toml b/Perennial/Code/os.toml
index 171e70c78..fe90234ff 100644
--- a/Perennial/Code/os.toml
+++ b/Perennial/Code/os.toml
@@ -5,7 +5,8 @@
 # `ErrNoDeadline`/`ErrDeadlineExceeded` and `CopyFileRange`/`Splice` function values, and `init.0`
 # (`Args = runtime_args()` unless `runtime.GOOS` is "windows", a constant goose emits as its value).
 # Trusted models (TrustedCode/os.lean):
-# * `runtime_args` (a `go:linkname` into the runtime, no Go body): an arbitrary `[]string`;
+# * `runtime_args` (a `go:linkname` into the runtime, no Go body): an arbitrary `[]string`, a call
+#   of `internal/gomodel.ChooseStrings`;
 # * `Stdout`, `Stderr` (`NewFile(uintptr(syscall.Stdout), "/dev/stdout")`, ...): `Stdout` does
 #   nothing (the variable is not allocated, code using it is stuck; it is to get a real model,
 #   perennial#663), `Stderr` allocates its variable and stores a fresh pointer whose
```

### Perennial/Code/syscall.toml  (tier 0, goose-config)

```diff
diff --git a/Perennial/Code/syscall.toml b/Perennial/Code/syscall.toml
index 6014dd9b4..023d38f35 100644
--- a/Perennial/Code/syscall.toml
+++ b/Perennial/Code/syscall.toml
@@ -1,12 +1,10 @@
-# syscall: the types, and the package-level variable initializers (what importing syscall runs).
-# Two pieces have no Go body or no modelled effect; they are trusted models
-# (TrustedCode/syscall.lean):
-# * `runtime_envs` (`env_unix.go`, a `go:linkname` into the runtime): an arbitrary `[]string`;
-# * `init.0` (`rlimit.go`: raises the soft RLIMIT_NOFILE through the raw `prlimit` system call):
-#   a no-op. The changed limit is only observable by `exec` (and `Getrlimit`), which Perennial
-#   does not model (the user's decision, fix-semantics Case 33);
-# * `Exit` (`syscall.go`, a body-less declaration the runtime provides, `syscall_Exit`): the
-#   process exits, `AngelicExit`.
+# syscall: the types, and the package-level variable initializers and `init` (what importing
+# syscall runs). `init.0` (`rlimit.go`: raises the soft RLIMIT_NOFILE to its hard limit minus one,
+# and records the original in `origRlimitNofile`) is translated, with `Getrlimit` and `setrlimit`,
+# over the model of the system call `prlimit1` (below). Trusted models (TrustedCode/syscall.lean) of
+# two body-less declarations the runtime provides (go:linkname pushes): `runtime_envs`
+# (`env_unix.go`): an arbitrary `[]string`, a call of `internal/gomodel.ChooseStrings`; `Exit`
+# (`syscall.go`, `syscall_Exit`): the process exits, `AngelicExit`.
 # `Setenv`, `Unsetenv`, `Clearenv` and the runtime's hooks `runtimeSetenv`/`runtimeUnsetenv`/
 # `runtimeClearenv` stay untranslated (a call is stuck). Keep it so, or make them stuck on the key
 # "GODEBUG": gc's runtime re-reads GODEBUG there, and the Go models that read a GODEBUG setting once
@@ -18,12 +16,20 @@ translate = ["!*",
   "Stdin", "Stdout", "Stderr",
   "errEAGAIN", "errEINVAL", "errENOENT",
   "errors", "signals", "_",
+  "init.0", "origRlimitNofile", "Getrlimit", "setrlimit", "adjustFileLimit", "errnoErr",
   # the constants these initializers use
-  "SYS_FCNTL", "EAGAIN", "EINVAL", "ENOENT",
+  "SYS_FCNTL", "EAGAIN", "EINVAL", "ENOENT", "RLIMIT_NOFILE",
 ]
-trusted = ["runtime_envs", "init.0", "Exit"]
+trusted = ["runtime_envs", "Exit"]
 
-imports = ["!*", "sync"]
+imports = ["!*", "sync", "sync/atomic", "internal/gomodel"]
 
 # translate the definitions of all type declarations goose supports
 translate_types = true
+
+# The Go model (goose/model/overlay/syscall): each declaration's MODEL: comment says why it has at
+# least Go's behaviours. `prlimit1` (`zsyscall_linux_amd64.go`, the `prlimit64` system call through `RawSyscall6` of `uintptr(unsafe.Pointer(...))` arguments): reads
+# `*newlimit`, may write arbitrary limits to `*old`, returns an arbitrary errno's error.
+[model]
+dir = "goose/model/overlay/syscall"
+replaces = ["prlimit1"]
```

### Perennial/TrustedCode/fmt.lean  (tier 0, trusted-model)

```diff
diff --git a/Perennial/TrustedCode/fmt.lean b/Perennial/TrustedCode/fmt.lean
index 22f6739ea..bf2e46634 100644
--- a/Perennial/TrustedCode/fmt.lean
+++ b/Perennial/TrustedCode/fmt.lean
@@ -1,3583 +1,57 @@
 /-
-Trusted code for the Go `fmt` package, in namespace `fmt` (as the generated
-package).
-
-`Sprintf` and the printer it runs are goose's translation of the real `fmt` (`Perennial/Code/fmt.toml`,
-perennial#671 stage 1). Until stage 2 retires them, `Printf`, `Fprintf`, `Fprint` and `Errorf` are
-still the models here, each goose's translation of the Go its docstring quotes, with the edits it
-names; they do not use the real printer (nor its pool `ppFree`). They share `doPrintf`, which formats the common directives of
-arguments that Go formats without calling any of their methods (`inert`) exactly (`formatArg`), and
-the common directives of a `[]byte` or a `[]string` (`formatSlice`, reading its bytes or elements, as Go does),
-and from the first other directive on gives an arbitrary string while calling what Go calls of the
-arguments: their `Error()` or `String()` under the verbs `v s x X q` (`visitRest`, `visitArg`).
-`Errorf` then returns what Go's `errorf` returns: `errors.New`, a `*wrapError` or a `*wrapErrors`,
-by its `%w` directives. `Fprint` calls what Go calls of each operand under `%v` (`visitArg`) and
-writes an arbitrary string. Where the model cannot follow Go (a `Format` or `GoString` method Go would
-call, a `reflect.Value` under a method verb, which Go's `printArg` unwraps (the model tells it by its
-`CanInterface() bool` method), reflection into a struct,
-pointer, map or slice (other than a `[]byte` or a `[]string`), an argument index or a `*` width), it is stuck (`notModelled`). The model's Go is also in `goose/model/fmt/model_test.go`, which
-`goose/model/fmt/model_diff_test.go` runs against Go's `fmt`: same output (each arbitrary string
-standing for any string), same method calls in the same order, same error kind, on every call the
-model is not stuck on, and the model is not stuck on any call the specs admit (`fmt.argsOk`; `Fprint`'s, `fmt.printArgOk`).
--/
-module
-
-public import Perennial.Golang.Defn.Pre
-public import Perennial.Code.errors
-public import Perennial.TrustedCode.arbitraryString
-public import Perennial.Code.io
-
-@[expose] public section
-
-set_option linter.iris.style.nameCheck false
-
-namespace Perennial
-
-namespace fmt
-section code
-variable [GooseExts] [GoGlobalContext]
-
-/-- At `format[i]`, a `%`: whether an integer directive follows, with its width and the index
-after it (helpers of the model's `doPrintf`, like those below, not functions of package `fmt`).
-Goose's translation of
-
-```go
-func intVerb(format string, i int) (int, int, bool) {
-	if i+1 < len(format) && (format[i+1] == 'd' || format[i+1] == 'v') {
-		return 0, i + 2, true
-	}
-	if i+1 < len(format) && format[i+1] == '0' {
-		j := i + 2
-		var width int
-		for j < len(format) && '0' <= format[j] && format[j] <= '9' && width <= 1000000 {
-			width = width*10 + int(format[j]-'0')
-			j++
-		}
-		if j > i+2 && j < len(format) && format[j] == 'd' && width <= 1000000 {
-			return width, j + 1, true
-		}
-	}
-	return 0, 0, false
-}
-```
-
-That is, `%d` and `%v` (width 0), and `%0Nd` with a decimal width `N` of one or more digits, at most
-`10^6` (Go's `fmt` refuses a larger one, stopping as this loop does). -/
-noncomputable def intVerb : val :=
-  (LamV "format"
-  (Lam "i"
-  (App (Val exceptionDo)
-  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (Var "i"))
-  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Pair (Pair (Val #(W64 0)) (Val #(W64 0))) (Val #false)))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 48)))) (Val #false)))
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
-  (Let "j" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "width" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (If (If (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "j")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2)))))) (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "j")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (Val #false)) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "j")))) (Val #(W8 100)))) (Val #false)) (App (Val (GoInstruction (GoOp GoLe go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "width")) (Val #(W64 1000000)))) (Val #false)))
-  (App (Val doReturn)
-  (Pair (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "width")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "j")) (Val #(W64 1))))) (Val #true)))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (App (App (Val doFor) (Lam BAnon
-  (If (If (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "j")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoLe go.byte))) (Pair (Val #(W8 48)) (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "j")))))) (Val #false)) (App (Val (GoInstruction (GoOp GoLe go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "j")))) (Val #(W8 57)))) (Val #false)) (App (Val (GoInstruction (GoOp GoLe go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "width")) (Val #(W64 1000000)))) (Val #false)))) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoOp GoMul go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "width")) (Val #(W64 10)))) (App (Val (GoInstruction (Convert go.byte go.int))) (App (Val (GoInstruction (GoOp GoSub go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "j")))) (Val #(W8 48)))))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "j") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "j")) (Val #(W64 1)))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "width") (Var "$r0"))))))))
-  (Lam BAnon
-  (Val #())))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "j") (Var "$r0")))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 100)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 118))))) (Val #false)))
-  (App (Val doReturn)
-  (Pair (Pair (Val #(W64 0)) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))) (Val #true)))
-  (App (Val doExecute)
-  (Val #())))))))))
-
-/-- The integer an argument holds, as a sign and a magnitude, if its dynamic type is one of Go's
-integer types. Goose's translation of
-
-```go
-func intArg(x any) (bool, uint64, bool) {
-	var n int64
-	if v, ok := x.(int); ok {
-		n = int64(v)
-	} else if v, ok := x.(int64); ok {
-		n = v
-	} else if v, ok := x.(int32); ok {
-		n = int64(v)
-	} else if v, ok := x.(int16); ok {
-		n = int64(v)
-	} else if v, ok := x.(int8); ok {
-		n = int64(v)
-	} else if v, ok := x.(uint); ok {
-		return false, uint64(v), true
-	} else if v, ok := x.(uint64); ok {
-		return false, v, true
-	} else if v, ok := x.(uint32); ok {
-		return false, uint64(v), true
-	} else if v, ok := x.(uint16); ok {
-		return false, uint64(v), true
-	} else if v, ok := x.(uint8); ok {
-		return false, uint64(v), true
-	} else {
-		return false, 0, false
-	}
-	if n < 0 {
-		return true, uint64(-n), true
-	}
-	return false, uint64(n), true
-}
-``` -/
-noncomputable def intArg : val :=
-  (LamV "x"
-  (App (Val exceptionDo)
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
-  (Let "n" (App (Val (GoInstruction (GoAlloc go.int64))) (App (Val (GoInstruction (GoZeroVal go.int64))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Pair (Pair (Val #false) (App (Val (GoInstruction (Convert go.int64 go.uint64))) (App (Val (GoInstruction (GoLoad go.int64))) (Var "n")))) (Val #true)))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.int64))) (Pair (App (Val (GoInstruction (GoLoad go.int64))) (Var "n")) (Val #(W64 0)))))
-  (App (Val doReturn)
-  (Pair (Pair (Val #true) (App (Val (GoInstruction (Convert go.int64 go.uint64))) (App (Val (GoInstruction (GoUnOp GoNeg go.int64))) (App (Val (GoInstruction (GoLoad go.int64))) (Var "n"))))) (Val #true)))
-  (App (Val doExecute)
-  (Val #()))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.int))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (App (Val (GoInstruction (Convert go.int go.int64))) (App (Val (GoInstruction (GoLoad go.int))) (Var "v")))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.int64))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.int64))) (App (Val (GoInstruction (GoZeroVal go.int64))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int64))) (Var "v"))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.int32))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.int32))) (App (Val (GoInstruction (GoZeroVal go.int32))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (App (Val (GoInstruction (Convert go.int32 go.int64))) (App (Val (GoInstruction (GoLoad go.int32))) (Var "v")))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.int16))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.int16))) (App (Val (GoInstruction (GoZeroVal go.int16))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (App (Val (GoInstruction (Convert go.int16 go.int64))) (App (Val (GoInstruction (GoLoad go.int16))) (Var "v")))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.int8))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.int8))) (App (Val (GoInstruction (GoZeroVal go.int8))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (App (Val (GoInstruction (Convert go.int8 go.int64))) (App (Val (GoInstruction (GoLoad go.int8))) (Var "v")))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.uint))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint))) (App (Val (GoInstruction (GoZeroVal go.uint))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (Val doReturn)
-  (Pair (Pair (Val #false) (App (Val (GoInstruction (Convert go.uint go.uint64))) (App (Val (GoInstruction (GoLoad go.uint))) (Var "v")))) (Val #true)))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.uint64))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (Val doReturn)
-  (Pair (Pair (Val #false) (App (Val (GoInstruction (GoLoad go.uint64))) (Var "v"))) (Val #true)))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.uint32))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint32))) (App (Val (GoInstruction (GoZeroVal go.uint32))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (Val doReturn)
-  (Pair (Pair (Val #false) (App (Val (GoInstruction (Convert go.uint32 go.uint64))) (App (Val (GoInstruction (GoLoad go.uint32))) (Var "v")))) (Val #true)))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.uint16))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint16))) (App (Val (GoInstruction (GoZeroVal go.uint16))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (Val doReturn)
-  (Pair (Pair (Val #false) (App (Val (GoInstruction (Convert go.uint16 go.uint64))) (App (Val (GoInstruction (GoLoad go.uint16))) (Var "v")))) (Val #true)))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.uint8))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint8))) (App (Val (GoInstruction (GoZeroVal go.uint8))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (Val doReturn)
-  (Pair (Pair (Val #false) (App (Val (GoInstruction (Convert go.uint8 go.uint64))) (App (Val (GoInstruction (GoLoad go.uint8))) (Var "v")))) (Val #true)))
-  (App (Val doReturn)
-  (Pair (Pair (Val #false) (Val #(W64 0))) (Val #false))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint8))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint16))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint32))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int8))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int16))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int32))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "v") (Var "$r0")))))))))))))))))
-
-/-- The integer an argument holds, as a sign and a magnitude, if its dynamic type is a type whose
-underlying type is one of Go's integer types (a named integer type, `type LeaseID int64`) and that
-implements none of `fmt.Formatter`, `fmt.Stringer` and `error`: Go's `printArg` then calls
-`handleMethods`, which finds no method to call, and `printValue` formats `reflect.ValueOf(x)`
-by its kind, as `fmtInteger` formats the underlying integer. (`fmt.GoStringer` is consulted
-only by `%#v`, which the model does not format.) Goose's translation (by the goose of this
-revision) of
-
-```go
-func namedIntArg(x any) (bool, uint64, bool) {
-	if _, ok := x.(interface{ Format(State, rune) }); ok {
-		return false, 0, false
-	}
-	if _, ok := x.(interface{ String() string }); ok {
-		return false, 0, false
-	}
-	if _, ok := x.(error); ok {
-		return false, 0, false
-	}
-	var n int64
-	if v, ok := underlyingAs[int](x); ok {
-		n = int64(v)
-	} else if v, ok := underlyingAs[int64](x); ok {
-		n = v
-	} else if v, ok := underlyingAs[int32](x); ok {
-		n = int64(v)
-	} else if v, ok := underlyingAs[int16](x); ok {
-		n = int64(v)
-	} else if v, ok := underlyingAs[int8](x); ok {
-		n = int64(v)
-	} else if v, ok := underlyingAs[uint](x); ok {
-		return false, uint64(v), true
-	} else if v, ok := underlyingAs[uint64](x); ok {
-		return false, v, true
-	} else if v, ok := underlyingAs[uint32](x); ok {
-		return false, uint64(v), true
-	} else if v, ok := underlyingAs[uint16](x); ok {
-		return false, uint64(v), true
-	} else if v, ok := underlyingAs[uint8](x); ok {
-		return false, uint64(v), true
-	} else {
-		return false, 0, false
-	}
-	if n < 0 {
-		return true, uint64(-n), true
-	}
-	return false, uint64(n), true
-}
-```
-
-where `State` is `fmt.State` and `underlyingAs[T](x)` is a stub `func underlyingAs[T any](x any)
-(T, bool)`, with two edits: goose's call `FuncResolve underlyingAs [T] #()` is replaced by the
-instruction `TypeAssertUnderlying2 T` (`reflect.ValueOf(x)` read at `T`'s kind, which plain Go
-cannot express), and the scratch package's `State.ty` by `go.GoType.Named go!"fmt.State" []`
-(`fmt.State.ty`). -/
-noncomputable def namedIntArg : val :=
-  (LamV "x"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
-  (Let "$res2" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "n" (App (Val (GoInstruction (GoAlloc go.int64))) (App (Val (GoInstruction (GoZeroVal go.int64))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Val #false)
-  (Let "$r1" (App (Val (GoInstruction (Convert go.int64 go.uint64))) (App (Val (GoInstruction (GoLoad go.int64))) (Var "n")))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.int64))) (Pair (App (Val (GoInstruction (GoLoad go.int64))) (Var "n")) (Val #(W64 0)))))
-  (Let "$r0" (Val #true)
-  (Let "$r1" (App (Val (GoInstruction (Convert go.int64 go.uint64))) (App (Val (GoInstruction (GoUnOp GoNeg go.int64))) (App (Val (GoInstruction (GoLoad go.int64))) (Var "n"))))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (GoInstruction (TypeAssertUnderlying2 go.int))) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (App (Val (GoInstruction (Convert go.int go.int64))) (App (Val (GoInstruction (GoLoad go.int))) (Var "v")))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (GoInstruction (TypeAssertUnderlying2 go.int64))) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.int64))) (App (Val (GoInstruction (GoZeroVal go.int64))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int64))) (Var "v"))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (GoInstruction (TypeAssertUnderlying2 go.int32))) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.int32))) (App (Val (GoInstruction (GoZeroVal go.int32))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (App (Val (GoInstruction (Convert go.int32 go.int64))) (App (Val (GoInstruction (GoLoad go.int32))) (Var "v")))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (GoInstruction (TypeAssertUnderlying2 go.int16))) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.int16))) (App (Val (GoInstruction (GoZeroVal go.int16))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (App (Val (GoInstruction (Convert go.int16 go.int64))) (App (Val (GoInstruction (GoLoad go.int16))) (Var "v")))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (GoInstruction (TypeAssertUnderlying2 go.int8))) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.int8))) (App (Val (GoInstruction (GoZeroVal go.int8))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (App (Val (GoInstruction (Convert go.int8 go.int64))) (App (Val (GoInstruction (GoLoad go.int8))) (Var "v")))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (GoInstruction (TypeAssertUnderlying2 go.uint))) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint))) (App (Val (GoInstruction (GoZeroVal go.uint))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #false)
-  (Let "$r1" (App (Val (GoInstruction (Convert go.uint go.uint64))) (App (Val (GoInstruction (GoLoad go.uint))) (Var "v")))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (GoInstruction (TypeAssertUnderlying2 go.uint64))) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #false)
-  (Let "$r1" (App (Val (GoInstruction (GoLoad go.uint64))) (Var "v"))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (GoInstruction (TypeAssertUnderlying2 go.uint32))) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint32))) (App (Val (GoInstruction (GoZeroVal go.uint32))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #false)
-  (Let "$r1" (App (Val (GoInstruction (Convert go.uint32 go.uint64))) (App (Val (GoInstruction (GoLoad go.uint32))) (Var "v")))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (GoInstruction (TypeAssertUnderlying2 go.uint16))) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint16))) (App (Val (GoInstruction (GoZeroVal go.uint16))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #false)
-  (Let "$r1" (App (Val (GoInstruction (Convert go.uint16 go.uint64))) (App (Val (GoInstruction (GoLoad go.uint16))) (Var "v")))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (GoInstruction (TypeAssertUnderlying2 go.uint8))) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint8))) (App (Val (GoInstruction (GoZeroVal go.uint8))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #false)
-  (Let "$r1" (App (Val (GoInstruction (Convert go.uint8 go.uint64))) (App (Val (GoInstruction (GoLoad go.uint8))) (Var "v")))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (Let "$r0" (Val #false)
-  (Let "$r1" (Val #(W64 0))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0")))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint8))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint16))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint32))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int8))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int16))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int32))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "v") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "v") (Var "$r0"))))))))))))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #false)
-  (Let "$r1" (Val #(W64 0))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0"))))))))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #false)
-  (Let "$r1" (Val #(W64 0))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0"))))))))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"Format" (go.signature.Signature [(go.GoType.Named go!"fmt.State" []), go.rune] false []))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #false)
-  (Let "$r1" (Val #(W64 0))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0"))))))))))))
-  (Pair (Pair (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.uint64))) (Var "$res1"))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res2"))))))))
-
-/-- The integer an argument holds, as a sign and a magnitude: that of `intArg` (one of Go's ten
-integer types), or else of `namedIntArg` (a named integer type without formatting methods).
-Goose's translation (by the goose of this revision) of
-
-```go
-func anyIntArg(x any) (bool, uint64, bool) {
-	neg, mag, ok := intArg(x)
-	if ok {
-		return neg, mag, true
-	}
-	return namedIntArg(x)
-}
-```
-
-with the calls running `fmt.intArg` and `fmt.namedIntArg` above (goose's `FuncResolve f [] #()`
-replaced by `f`). -/
-noncomputable def anyIntArg : val :=
-  (LamV "x"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
-  (Let "$res2" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val intArg) (Var "$a0")))
-  (Let "$ret0" (Fst (Fst (Var "__p")))
-  (Let "$ret1" (Snd (Fst (Var "__p")))
-  (Let "$ret2" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "$r2" (Var "$ret2")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "mag" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
-  (Let "neg" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val namedIntArg) (Var "$a0")))
-  (Let "$ret0" (Fst (Fst (Var "__p")))
-  (Let "$ret1" (Snd (Fst (Var "__p")))
-  (Let "$ret2" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "$r2" (Var "$ret2")
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))))))))
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.bool))) (Var "neg"))
-  (Let "$r1" (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag"))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "mag") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "neg") (Var "$r0")))))))))))))))))
-  (Pair (Pair (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.uint64))) (Var "$res1"))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res2"))))))))
-
-/-- The decimal of the integer of sign `neg` and magnitude `mag`, with leading zeros up to width
-`width`, the sign before them (Go's `fmtInteger` with the `0` flag). Goose's translation of
-
-```go
-func formatInt(neg bool, mag uint64, width int) string {
-	var digits string
-	for {
-		digits = string([]byte{byte(mag%10) + '0'}) + digits
-		mag = mag / 10
-		if mag == 0 {
-			break
-		}
-	}
-	if neg {
-		width--
-	}
-	for len(digits) < width {
-		digits = "0" + digits
-	}
-	if neg {
-		return "-" + digits
-	}
-	return digits
-}
-``` -/
-noncomputable def formatInt : val :=
-  (LamV "neg"
-  (Lam "mag"
-  (Lam "width"
-  (App (Val exceptionDo)
-  (Let "width" (App (Val (GoInstruction (GoAlloc go.int))) (Var "width"))
-  (Let "mag" (App (Val (GoInstruction (GoAlloc go.uint64))) (Var "mag"))
-  (Let "neg" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "neg"))
-  (Let "digits" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (App (Val (GoInstruction (GoLoad go.string))) (Var "digits")))))
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "neg"))
-  (App (Val doReturn)
-  (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (Val #(go!"-")) (App (Val (GoInstruction (GoLoad go.string))) (Var "digits")))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (App (App (Val doFor) (Lam BAnon
-  (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "digits"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))) (App (Val (GoInstruction (GoLoad go.int))) (Var "width")))))) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (Val #(go!"0")) (App (Val (GoInstruction (GoLoad go.string))) (Var "digits"))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "digits") (Var "$r0")))))))
-  (Lam BAnon
-  (Val #()))))))
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "neg"))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "width") (App (Val (GoInstruction (GoOp GoSub go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "width")) (Val #(W64 1)))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (App (App (Val doFor) (Lam BAnon
-  (Val #true))) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (App (Val (GoInstruction (GoOp GoPlus go.byte))) (Pair (App (Val (GoInstruction (Convert go.uint64 go.byte))) (App (Val (GoInstruction (GoOp GoRemainder go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag")) (Val #(W64 10))))) (Val #(W8 48))))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0")))])))) (App (Val (GoInstruction (GoLoad go.string))) (Var "digits"))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoDiv go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag")) (Val #(W64 10))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag")) (Val #(W64 0)))))
-  (App (Val doBreak) (Val #()))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "mag") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "digits") (Var "$r0"))))))))
-  (Lam BAnon
-  (Val #()))))))))))))
-
-/-- The lowercase hexadecimal of the integer of sign `neg` and magnitude `mag`, without a `0x`
-prefix, the sign before the digits (Go's `fmtInteger` in base 16 with no flags, width or
-precision: `Sprintf("%x", -255)` is `"-ff"`). Goose's translation (by the goose of this
-revision, with its function results in cells `$resI`) of
-
-```go
-func formatHex(neg bool, mag uint64) string {
-	var digits string
-	for {
-		d := byte(mag % 16)
-		if d < 10 {
-			d = '0' + d
-		} else {
-			d = 'a' + (d - 10)
-		}
-		digits = string([]byte{d}) + digits
-		mag = mag / 16
-		if mag == 0 {
-			break
-		}
-	}
-	if neg {
-		return "-" + digits
-	}
-	return digits
-}
-``` -/
-noncomputable def formatHex : val :=
-  (LamV "neg"
-  (Lam "mag"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "mag" (App (Val (GoInstruction (GoAlloc go.uint64))) (Var "mag"))
-  (Let "neg" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "neg"))
-  (Let "digits" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "digits"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "neg"))
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (Val #(go!"-")) (App (Val (GoInstruction (GoLoad go.string))) (Var "digits"))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (App (App (Val doFor) (Lam BAnon
-  (Val #true))) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (Convert go.uint64 go.byte))) (App (Val (GoInstruction (GoOp GoRemainder go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag")) (Val #(W64 16)))))
-  (Let "d" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (App (Val (GoInstruction (GoLoad go.byte))) (Var "d"))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0")))])))) (App (Val (GoInstruction (GoLoad go.string))) (Var "digits"))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoDiv go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag")) (Val #(W64 16))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag")) (Val #(W64 0)))))
-  (App (Val doBreak) (Val #()))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "mag") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "digits") (Var "$r0"))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "d")) (Val #(W8 10)))))
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.byte))) (Pair (Val #(W8 48)) (App (Val (GoInstruction (GoLoad go.byte))) (Var "d"))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "d") (Var "$r0")))))
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.byte))) (Pair (Val #(W8 97)) (App (Val (GoInstruction (GoOp GoSub go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "d")) (Val #(W8 10))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "d") (Var "$r0")))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "d") (Var "$r0")))))))))
-  (Lam BAnon
-  (Val #()))))))))
-  (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0"))))))
-
-/-- The string an argument holds, if its dynamic type is `string` or a type whose underlying type
-is `string` (a named string type, `type UID string`) and that implements none of `fmt.Formatter`,
-`fmt.Stringer` and `error`: Go's `printArg` formats a `string` with `fmtString`, and a value of a
-named string type falls to `handleMethods`, which finds no method to call, and `printValue`
-formats `reflect.ValueOf(x)` by its kind, `String`, with `fmtString` of `Value.String()`, its
-string. (A `string` has no methods, so the checks below are false for it. `fmt.GoStringer` is
-consulted only by `%#v`, which the model does not format.) Goose's translation (by the goose of
-this revision) of
-
-```go
-func strArg(x any) (string, bool) {
-	if _, ok := x.(interface{ Format(State, rune) }); ok {
-		return "", false
-	}
-	if _, ok := x.(interface{ String() string }); ok {
-		return "", false
-	}
-	if _, ok := x.(error); ok {
-		return "", false
-	}
-	return underlyingAs[string](x)
-}
-```
-
-with the two edits of `namedIntArg`: goose's call `FuncResolve underlyingAs [go.string] #()` is
-replaced by the instruction `TypeAssertUnderlying2 go.string` (`reflect.ValueOf(x).String()` for a
-value of kind `String`), and the scratch package's `State.ty` by
-`go.GoType.Named go!"fmt.State" []`. -/
-noncomputable def strArg : val :=
-  (LamV "x"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (GoInstruction (TypeAssertUnderlying2 go.string))) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #(go!""))
-  (Let "$r1" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0")))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0"))))))))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #(go!""))
-  (Let "$r1" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0")))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0"))))))))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"Format" (go.signature.Signature [(go.GoType.Named go!"fmt.State" []), go.rune] false []))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #(go!""))
-  (Let "$r1" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0")))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0"))))))))))))
-  (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res1")))))))
-
-/-- At `format[i]`, a `%`: the directive's output for the argument `x` and the index after it, if
-the model formats it: `%s` or `%v` of a string (`strArg`: a `string`, or a named string type
-without formatting methods), `%x` of an integer (`anyIntArg`), or an integer directive (`intVerb`,
-which takes `%v` too) of an integer. Goose's translation (by the goose of this revision, with its function
-results in cells `$resI`) of
-
-```go
-func formatArg(format string, i int, x any) (string, int, bool) {
-	if i+1 < len(format) && format[i+1] == 's' {
-		s, ok := strArg(x)
-		return s, i + 2, ok
-	}
-	if i+1 < len(format) && format[i+1] == 'v' {
-		if s, ok := strArg(x); ok {
-			return s, i + 2, true
-		}
-	}
-	if i+1 < len(format) && format[i+1] == 'x' {
-		neg, mag, ok := anyIntArg(x)
-		if !ok {
-			return "", 0, false
-		}
-		return formatHex(neg, mag), i + 2, true
-	}
-	width, next, ok := intVerb(format, i)
-	if !ok {
-		return "", 0, false
-	}
-	neg, mag, ok2 := anyIntArg(x)
-	if !ok2 {
-		return "", 0, false
-	}
-	return formatInt(neg, mag, width), next, true
-}
-```
-
-with the calls running `fmt.strArg`, `fmt.intVerb`, `fmt.anyIntArg`, `fmt.formatInt` and
-`fmt.formatHex` above
-(goose's `FuncResolve f [] #()` replaced by `f`, the only edit). `%v` of a `string` is the string
-itself, as `%s` gives it: Go's `fmt` documents the default format `%v` of a string as `%s`, and
-`printArg` formats a `string` argument with `fmtString`, whose `'v'` case (without the `#` flag) is
-`fmtS`, the `'s'` case, which copies the bytes unchanged when there is no precision or width.
-`goose/model/fmt/sprintf_test.go` checks that `fmt.Sprintf` gives every string, byte for byte, for
-`%v` as for `%s` (the empty string, `%`, invalid UTF-8, NUL), and the same for a named string type
-without formatting methods; a named string type with a `String`, `Error` or `Format` method
-(whose call the model does not make) makes the rest of the output arbitrary; `doPrintf` calls
-`formatArg` only for an argument `inert` says has none of these methods. -/
-noncomputable def formatArg : val :=
-  (LamV "format"
-  (Lam "i"
-  (Lam "x"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (Let "$res2" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
-  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (Var "i"))
-  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (Let "$a1" (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))
-  (App (App (Val intVerb) (Var "$a0")) (Var "$a1"))))
-  (Let "$ret0" (Fst (Fst (Var "__p")))
-  (Let "$ret1" (Snd (Fst (Var "__p")))
-  (Let "$ret2" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "$r2" (Var "$ret2")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "next" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (Let "width" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val anyIntArg) (Var "$a0")))
-  (Let "$ret0" (Fst (Fst (Var "__p")))
-  (Let "$ret1" (Snd (Fst (Var "__p")))
-  (Let "$ret2" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "$r2" (Var "$ret2")
-  (Let "ok2" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "mag" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
-  (Let "neg" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.bool))) (Var "neg"))
-  (Let "$a1" (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag"))
-  (Let "$a2" (App (Val (GoInstruction (GoLoad go.int))) (Var "width"))
-  (App (App (App (Val formatInt) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
-  (Let "$r1" (App (Val (GoInstruction (GoLoad go.int))) (Var "next"))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
-  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok2")))
-  (Let "$r0" (Val #(go!""))
-  (Let "$r1" (Val #(W64 0))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "mag") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "neg") (Var "$r0")))))))))))))))))
-  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok")))
-  (Let "$r0" (Val #(go!""))
-  (Let "$r1" (Val #(W64 0))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "next") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "width") (Var "$r0")))))))))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 120)))) (Val #false)))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val anyIntArg) (Var "$a0")))
-  (Let "$ret0" (Fst (Fst (Var "__p")))
-  (Let "$ret1" (Snd (Fst (Var "__p")))
-  (Let "$ret2" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "$r2" (Var "$ret2")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "mag" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
-  (Let "neg" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.bool))) (Var "neg"))
-  (Let "$a1" (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag"))
-  (App (App (Val formatHex) (Var "$a0")) (Var "$a1"))))
-  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
-  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok")))
-  (Let "$r0" (Val #(go!""))
-  (Let "$r1" (Val #(W64 0))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "mag") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "neg") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 118)))) (Val #false)))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val strArg) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
-  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0"))))))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 115)))) (Val #false)))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val strArg) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
-  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
-  (Let "$r2" (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0"))))))))))))
-  (App (Val doExecute)
-  (Val #()))))))))
-  (Pair (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.int))) (Var "$res1"))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res2"))))))))))
-
-/-- The hexadecimal digit of `d` (below 16), lowercase or uppercase (a helper of `formatSlice`). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func hexNibble(d byte, upper bool) byte {
-	if d < 10 {
-		return '0' + d
-	}
-	if upper {
-		return 'A' + (d - 10)
-	}
-	return 'a' + (d - 10)
-}
-```
-
-unedited. -/
-noncomputable def hexNibble : val :=
-  (LamV "d"
-  (Lam "upper"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "upper" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "upper"))
-  (Let "d" (App (Val (GoInstruction (GoAlloc go.byte))) (Var "d"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.byte))) (Pair (Val #(W8 97)) (App (Val (GoInstruction (GoOp GoSub go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "d")) (Val #(W8 10))))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "upper"))
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.byte))) (Pair (Val #(W8 65)) (App (Val (GoInstruction (GoOp GoSub go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "d")) (Val #(W8 10))))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "d")) (Val #(W8 10)))))
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.byte))) (Pair (Val #(W8 48)) (App (Val (GoInstruction (GoLoad go.byte))) (Var "d"))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #())))))))
-  (App (Val (GoInstruction (GoLoad go.byte))) (Var "$res0"))))))
-
-/-- The byte `c` as `strconv.Quote` writes it inside the quotes, for `c` below `0x80` (a helper of `quoteBytes`): `\"` and `\\`, the bytes from `0x20` to `0x7E` themselves, the escapes `\a \b \f \n \r \t \v`, and `\xNN` for the other control bytes and `0x7F` (there `strconv`'s escaping depends on no table). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func quoteByte(c byte) string {
-	if c == '"' || c == '\\' {
-		return string([]byte{'\\', c})
-	}
-	if 0x20 <= c && c <= 0x7e {
-		return string([]byte{c})
-	}
-	if c == '\a' {
-		return `\a`
-	}
-	if c == '\b' {
-		return `\b`
-	}
-	if c == '\f' {
-		return `\f`
-	}
-	if c == '\n' {
-		return `\n`
-	}
-	if c == '\r' {
-		return `\r`
-	}
-	if c == '\t' {
-		return `\t`
-	}
-	if c == '\v' {
-		return `\v`
-	}
-	return string([]byte{'\\', 'x', hexNibble(c/16, false), hexNibble(c%16, false)})
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def quoteByte : val :=
-  (LamV "c"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "c" (App (Val (GoInstruction (GoAlloc go.byte))) (Var "c"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (Val #(W8 92))
-  (Let "$v1" (Val #(W8 120))
-  (Let "$v2" (Let "$a0" (App (Val (GoInstruction (GoOp GoDiv go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 16))))
-  (Let "$a1" (Val #false)
-  (App (App (Val hexNibble) (Var "$a0")) (Var "$a1"))))
-  (Let "$v3" (Let "$a0" (App (Val (GoInstruction (GoOp GoRemainder go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 16))))
-  (Let "$a1" (Val #false)
-  (App (App (Val hexNibble) (Var "$a0")) (Var "$a1"))))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0"))), (KeyedElement none (ElementExpression go.byte (Var "$v1"))), (KeyedElement none (ElementExpression go.byte (Var "$v2"))), (KeyedElement none (ElementExpression go.byte (Var "$v3")))])))))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 11)))))
-  (Let "$r0" (Val #(go!"\\v"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 9)))))
-  (Let "$r0" (Val #(go!"\\t"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 13)))))
-  (Let "$r0" (Val #(go!"\\r"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 10)))))
-  (Let "$r0" (Val #(go!"\\n"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 12)))))
-  (Let "$r0" (Val #(go!"\\f"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 8)))))
-  (Let "$r0" (Val #(go!"\\b"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 7)))))
-  (Let "$r0" (Val #(go!"\\a"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLe go.byte))) (Pair (Val #(W8 32)) (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")))) (App (Val (GoInstruction (GoOp GoLe go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 126)))) (Val #false)))
-  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (App (Val (GoInstruction (GoLoad go.byte))) (Var "c"))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0")))]))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 34)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 92))))))
-  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (Val #(W8 92))
-  (Let "$v1" (App (Val (GoInstruction (GoLoad go.byte))) (Var "c"))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0"))), (KeyedElement none (ElementExpression go.byte (Var "$v1")))])))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")))))
-
-/-- `strconv.Quote(string(b))`, as Go's `fmtQ` prints `%q` of a `[]byte` without flags, width or precision, when every byte of `b` is ASCII (below `0x80`): there `strconv`'s escaping depends on no table (`IsPrint` is true exactly from `0x20` to `0x7E`; `\"` and `\\`, the seven escapes `\a \b \f \n \r \t \v`, `\xNN` for the other control bytes and `0x7F`). `ok` is false when a byte is not ASCII, where `strconv` decodes UTF-8 and consults its printable-rune tables (`isPrint16`, ..., trusted with unknown contents): the model does not follow it. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func quoteBytes(b []byte) (string, bool) {
-	out := "\""
-	for _, c := range b {
-		if c >= 0x80 {
-			return "", false
-		}
-		out += quoteByte(c)
-	}
-	return out + "\"", true
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def quoteBytes : val :=
-  (LamV "b"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (Var "b"))
-  (Let "$r0" (Val #(go!"\""))
-  (Let "out" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Val #(go!"\""))))
-  (Let "$r1" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0")))))))))
-  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
-  (Let "c" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
-  (App (App (Val (slice.forRange go.byte)) (Var "$range"))
-  (Lam "$key"
-  (Lam "$value"
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.byte))) (Var "c"))
-  (App (Val quoteByte) (Var "$a0"))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGe go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 128)))))
-  (Let "$r0" (Val #(go!""))
-  (Let "$r1" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0")))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (Var "$key")))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "c") (Var "$value")))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (Var "$r0")))))))))
-  (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res1")))))))
-
-/-- `%v` and `%d` of the `[]byte` `b`, as Go's `fmtBytes` prints them: its bytes in decimal, separated by spaces, in brackets (a helper of `formatSlice`). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func decBytes(b []byte) string {
-	out := "["
-	for k, c := range b {
-		if k > 0 {
-			out += " "
-		}
-		out += formatInt(false, uint64(c), 0)
-	}
-	return out + "]"
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def decBytes : val :=
-  (LamV "b"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (Var "b"))
-  (Let "$r0" (Val #(go!"["))
-  (Let "out" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Val #(go!"]"))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
-  (Let "c" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
-  (Let "k" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (App (App (Val (slice.forRange go.byte)) (Var "$range"))
-  (Lam "$key"
-  (Lam "$value"
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Let "$a0" (Val #false)
-  (Let "$a1" (App (Val (GoInstruction (Convert go.byte go.uint64))) (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")))
-  (Let "$a2" (Val #(W64 0))
-  (App (App (App (Val formatInt) (Var "$a0")) (Var "$a1")) (Var "$a2"))))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "k")) (Val #(W64 0)))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Val #(go!" ")))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "k") (Var "$key")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "c") (Var "$value"))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (Var "$r0")))))))))
-  (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")))))
-
-/-- `%x` (`upper` false) and `%X` of the `[]byte` `b`, as Go's `fmtBytes` prints them: two hexadecimal characters a byte (a helper of `formatSlice`). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func hexBytes(b []byte, upper bool) string {
-	var out string
-	for _, c := range b {
-		out += string([]byte{hexNibble(c/16, upper), hexNibble(c%16, upper)})
-	}
-	return out
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def hexBytes : val :=
-  (LamV "b"
-  (Lam "upper"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "upper" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "upper"))
-  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (Var "b"))
-  (Let "out" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "out"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
-  (Let "c" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
-  (App (App (Val (slice.forRange go.byte)) (Var "$range"))
-  (Lam "$key"
-  (Lam "$value"
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (Let "$a0" (App (Val (GoInstruction (GoOp GoDiv go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 16))))
-  (Let "$a1" (App (Val (GoInstruction (GoLoad go.bool))) (Var "upper"))
-  (App (App (Val hexNibble) (Var "$a0")) (Var "$a1"))))
-  (Let "$v1" (Let "$a0" (App (Val (GoInstruction (GoOp GoRemainder go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 16))))
-  (Let "$a1" (App (Val (GoInstruction (GoLoad go.bool))) (Var "upper"))
-  (App (App (Val hexNibble) (Var "$a0")) (Var "$a1"))))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0"))), (KeyedElement none (ElementExpression go.byte (Var "$v1")))]))))))))))))
-  (App (Val doExecute)
-  (Var "$key")))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "c") (Var "$value")))))))))))))))
-  (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0"))))))
-
-/-- `%v` and `%s` of the `[]string` `ss`, as Go's `printValue` prints a slice: `[`, its elements separated by spaces (each by `fmtS`: a `string` has no method for `handleMethods` to call, and without flags, width or precision `fmtS` writes it as it is), `]` (a helper of `formatSlice`). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func joinStrings(ss []string) string {
-	out := "["
-	for k, s := range ss {
-		if k > 0 {
-			out += " "
-		}
-		out += s
-	}
-	return out + "]"
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def joinStrings : val :=
-  (LamV "ss"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "ss" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.string)))) (Var "ss"))
-  (Let "$r0" (Val #(go!"["))
-  (Let "out" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Val #(go!"]"))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "ss"))
-  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (Let "k" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (App (App (Val (slice.forRange go.string)) (Var "$range"))
-  (Lam "$key"
-  (Lam "$value"
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val (GoInstruction (GoLoad go.string))) (Var "s")))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "k")) (Val #(W64 0)))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Val #(go!" ")))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "k") (Var "$key")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$value"))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (Var "$r0")))))))))
-  (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")))))
-
-/-- At `format[i]`, a `%`: the output of the directive for the argument `x`, if it is of type `[]byte` or `[]string` (exactly: not a named type of either underlying type), and the index after it. Of a `[]byte`, as Go's `fmtBytes` prints it, if the directive is `%s`, `%v`, `%d`, `%x`, `%X` or `%q` without flags, width or precision (`%q` only of ASCII bytes, `quoteBytes`): `string(b)`; the decimal bytes in brackets, separated by spaces; two hexadecimal digits a byte. Of a `[]string`, as Go's `printValue` prints it (Go's `printArg` has no case for it and `handleMethods` finds no method on it, nor on its elements), if the directive is `%s` or `%v` without flags, width or precision (`joinStrings`). It reads every byte or element of `x` then, as Go does, and nothing otherwise (the type assertions only after the verb: the proofs of the calls that never reach them need no ownership). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func formatSlice(format string, i int, x any) (string, int, bool) {
-	if i+1 >= len(format) {
-		return "", 0, false
-	}
-	verb := format[i+1]
-	if verb != 's' && verb != 'v' && verb != 'd' && verb != 'x' && verb != 'X' && verb != 'q' {
-		return "", 0, false
-	}
-	if ss, ok := x.([]string); ok {
-		if verb == 's' || verb == 'v' {
-			return joinStrings(ss), i + 2, true
-		}
-		return "", 0, false
-	}
-	b, ok := x.([]byte)
-	if !ok {
-		return "", 0, false
-	}
-	if verb == 's' {
-		return string(b), i + 2, true
-	}
-	if verb == 'v' || verb == 'd' {
-		return decBytes(b), i + 2, true
-	}
-	if verb == 'x' || verb == 'X' {
-		return hexBytes(b, verb == 'X'), i + 2, true
-	}
-	if verb == 'q' {
-		s, ok := quoteBytes(b)
-		if !ok {
-			return "", 0, false
-		}
-		return s, i + 2, true
-	}
-	return "", 0, false
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def formatSlice : val :=
-  (LamV "format"
-  (Lam "i"
-  (Lam "x"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (Let "$res2" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
-  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (Var "i"))
-  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))
-  (Let "verb" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Val #(go!""))
-  (Let "$r1" (Val #(W64 0))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 113)))))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
-  (App (Val quoteBytes) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
-  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
-  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok")))
-  (Let "$r0" (Val #(go!""))
-  (Let "$r1" (Val #(W64 0))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0"))))))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 120)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 88))))))
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
-  (Let "$a1" (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 88))))
-  (App (App (Val hexBytes) (Var "$a0")) (Var "$a1"))))
-  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 118)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 100))))))
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
-  (App (Val decBytes) (Var "$a0")))
-  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 115)))))
-  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b")))
-  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok")))
-  (Let "$r0" (Val #(go!""))
-  (Let "$r1" (Val #(W64 0))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "b") (Var "$r0"))))))))))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.SliceType go.string)))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "ss" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.string)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.string)))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Val #(go!""))
-  (Let "$r1" (Val #(W64 0))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 115)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 118))))))
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "ss"))
-  (App (Val joinStrings) (Var "$a0")))
-  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
-  (Let "$r2" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #()))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.string)))) (Pair (Var "ss") (Var "$r0")))))))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (If (If (If (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 115))))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 118))))) (Val #false)) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 100))))) (Val #false)) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 120))))) (Val #false)) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 88))))) (Val #false)) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 113))))) (Val #false)))
-  (Let "$r0" (Val #(go!""))
-  (Let "$r1" (Val #(W64 0))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "verb") (Var "$r0")))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGe go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))))
-  (Let "$r0" (Val #(go!""))
-  (Let "$r1" (Val #(W64 0))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Val #()))))))))
-  (Pair (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.int))) (Var "$res1"))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res2"))))))))))
-
-/-- The model's stuck point, where it does not follow Go (a helper, not a function of package `fmt`):
-`Panic`, the primitive that takes no step (undefined behaviour, not a Go panic, which would be a
-`PanicV` a deferred `recover` can catch). Go does not panic there: the model is less defined than Go,
-and the specs exclude every call that reaches it. In the Go the docstrings quote, a call
-`notModelled()`. -/
-noncomputable def notModelled : val :=
-  (LamV BAnon (Panic "fmt: not modelled"))
-
-/-- `kindIs T`, for an integer type or `string` `T`: whether the argument's dynamic type has `T`'s
-underlying type, i.e. `reflect.ValueOf(x).Kind()` is `T`'s kind (a helper, not a function of
-package `fmt`): the second result of `TypeAssertUnderlying2 T` (`InterfaceSemantics`), which plain
-Go cannot express. In the Go the docstrings quote, a call of a stub `func kindIs[T any](x any)
-bool`. -/
-noncomputable def kindIs (T : go.GoType) : val :=
-  (LamV "y" (Snd (App (Val (GoInstruction (TypeAssertUnderlying2 T))) (Var "y"))))
-
-/-- The helper `isBasic` of the model (not a function of package `fmt`): whether x's dynamic type is one of the predeclared types that printArg formats by its type switch, without handleMethods (bool, the integer types, uintptr, float32, float64, string; not complex64 or complex128, which the model does not follow, nor []byte, which visitArg reads, nor reflect.Value, which printArg unwraps: visitArg is stuck on a Stringer with a CanInterface() bool method, as it has). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func isBasic(x any) bool {
-	switch x.(type) {
-	case bool, int, int8, int16, int32, int64, uint, uint8, uint16, uint32, uint64, uintptr,
-		float32, float64, string:
-		return true
-	}
-	return false
-}
-```
-
-unedited. -/
-noncomputable def isBasic : val :=
-  (LamV "x"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (Let "$y" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (Let "$ok" (If (Snd (App (Val (GoInstruction (TypeAssert2 go.string))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.float64))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.float32))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.uintptr))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.uint64))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.uint32))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.uint16))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.uint8))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.uint))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.int64))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.int32))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.int16))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.int8))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.int))) (Var "$y"))) (Val #true) (Snd (App (Val (GoInstruction (TypeAssert2 go.bool))) (Var "$y")))))))))))))))))
-  (Let "$x" (Var "$y")
-  (If (Var "$ok")
-  (Let "$r0" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #())))))))))
-  (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")))))
-
-/-- The helper `isIntKind` of the model (not a function of package `fmt`): whether x's dynamic type has an integer kind (one of Go's ten integer types as its underlying type; not uintptr). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func isIntKind(x any) bool {
-	return kindIs[int](x) || kindIs[int64](x) || kindIs[int32](x) || kindIs[int16](x) ||
-		kindIs[int8](x) || kindIs[uint](x) || kindIs[uint64](x) || kindIs[uint32](x) ||
-		kindIs[uint16](x) || kindIs[uint8](x)
-}
-```
-
-with these edits: goose's `FuncResolve kindIs [T] #()` replaced by `kindIs T` (the second result of `TypeAssertUnderlying2 T`). -/
-noncomputable def isIntKind : val :=
-  (LamV "x"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
-  (Let "$r0" (If (If (If (If (If (If (If (If (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (kindIs go.int)) (Var "$a0"))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (kindIs go.int64)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (kindIs go.int32)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (kindIs go.int16)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (kindIs go.int8)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (kindIs go.uint)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (kindIs go.uint64)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (kindIs go.uint32)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (kindIs go.uint16)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (kindIs go.uint8)) (Var "$a0"))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")))))
-
-/-- The helper `isStrKind` of the model (not a function of package `fmt`): whether x's dynamic type has kind String. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func isStrKind(x any) bool {
-	return kindIs[string](x)
-}
-```
-
-with these edits: goose's `FuncResolve kindIs [T] #()` replaced by `kindIs T` (the second result of `TypeAssertUnderlying2 T`). -/
-noncomputable def isStrKind : val :=
-  (LamV "x"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val (kindIs go.string)) (Var "$a0")))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")))))
-
-/-- The helper `hasFmtMethod` of the model (not a function of package `fmt`): whether x implements one of the interfaces handleMethods consults (Formatter, GoStringer, error, Stringer). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func hasFmtMethod(x any) bool {
-	if _, ok := x.(interface{ Format(State, rune) }); ok {
-		return true
-	}
-	if _, ok := x.(interface{ GoString() string }); ok {
-		return true
-	}
-	if _, ok := x.(error); ok {
-		return true
-	}
-	if _, ok := x.(interface{ String() string }); ok {
-		return true
-	}
-	return false
-}
-```
-
-with these edits: the scratch package's `State.ty` replaced by `go.GoType.Named go!"fmt.State" []` (`fmt.State.ty`). -/
-noncomputable def hasFmtMethod : val :=
-  (LamV "x"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0"))))))))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0"))))))))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"GoString" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0"))))))))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"Format" (go.signature.Signature [(go.GoType.Named go!"fmt.State" []), go.rune] false []))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0"))))))))))))
-  (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")))))
-
-/-- The helper `inert` of the model (not a function of package `fmt`): whether Go formats x, under any directive, without calling any of its methods or reading memory: nil, a predeclared basic type, or a type of integer or string kind that implements none of handleMethods' interfaces. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func inert(x any) bool {
-	if x == nil {
-		return true
-	}
-	if isBasic(x) {
-		return true
-	}
-	if hasFmtMethod(x) {
-		return false
-	}
-	if isStrKind(x) {
-		return true
-	}
-	return isIntKind(x)
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def inert : val :=
-  (LamV "x"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val isIntKind) (Var "$a0")))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val isStrKind) (Var "$a0")))
-  (Let "$r0" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val hasFmtMethod) (Var "$a0")))
-  (Let "$r0" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val isBasic) (Var "$a0")))
-  (Let "$r0" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.any))) (Pair (App (Val (GoInstruction (GoLoad go.any))) (Var "x")) (App (Val (GoInstruction (Convert go.untypedNil go.any))) (Val UntypedNil)))))
-  (Let "$r0" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")))))
-
-/-- The helper `allInert` of the model (not a function of package `fmt`): whether every argument is inert. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func allInert(a []any) bool {
-	for _, x := range a {
-		if !inert(x) {
-			return false
-		}
-	}
-	return true
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def allInert : val :=
-  (LamV "a"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (App (Val (GoInstruction (GoZeroVal go.any))) (Val #())))
-  (App (App (Val (slice.forRange go.any)) (Var "$range"))
-  (Lam "$key"
-  (Lam "$value"
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val inert) (Var "$a0"))))
-  (Let "$r0" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (Var "$key")))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.any))) (Pair (Var "x") (Var "$value")))))))))))))
-  (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")))))
-
-/-- The helper `parseDirective` of the model (not a function of package `fmt`) reads the directive whose bytes start at format[i], after its '%', as doPrintf does: flags among '#', '0', '+', '-', ' '; a decimal width; '.' and a decimal precision (only if a byte follows the '.'); the verb. It returns the verb (as an int; -1 if the format ends first, Go's %!(NOVERB)), whether the directive is %#v or %#w (Go's sharpV), and the index after it. ok is false where the model does not follow Go: a '*' width or precision, an argument index '[', or a width or precision of more than 7 digits. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func parseDirective(format string, i int) (int, bool, int, bool) {
-	var sharp bool
-	var phase int // 0: flags, 1: width, 2: precision
-	var n int     // digits read of the width or precision
-	for i < len(format) {
-		c := format[i]
-		if phase == 0 && c == '#' {
-			sharp = true
-			i++
-			continue
-		}
-		if phase == 0 && (c == '+' || c == '-' || c == '0' || c == ' ') {
-			i++
-			continue
-		}
-		if '0' <= c && c <= '9' {
-			if phase == 0 {
-				phase = 1
-				n = 1
-				i++
-				continue
-			}
-			if n >= 7 {
-				return 0, false, 0, false
-			}
-			n++
-			i++
-			continue
-		}
-		if phase < 2 && c == '.' && i+1 < len(format) {
-			phase = 2
-			n = 0
-			i++
-			continue
-		}
-		if c == '*' || c == '[' {
-			return 0, false, 0, false
-		}
-		return int(c), sharp && (c == 'v' || c == 'w'), i + 1, true
-	}
-	return -1, false, i, true
-}
-```
-
-unedited. -/
-noncomputable def parseDirective : val :=
-  (LamV "format"
-  (Lam "i"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "$res2" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (Let "$res3" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (Var "i"))
-  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
-  (Let "sharp" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "phase" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (Let "n" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (Convert go.untypedInt go.int))) (App (Val (GoInstruction (GoUnOp GoNeg go.untypedInt))) (Val #(1 : Int))))
-  (Let "$r1" (Val #false)
-  (Let "$r2" (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))
-  (Let "$r3" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res3") (Var "$r3")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0")))))))))))
-  (App (App (App (Val doFor) (Lam BAnon
-  (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))))) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))))
-  (Let "c" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (Convert go.byte go.int))) (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")))
-  (Let "$r1" (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "sharp")) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 118)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 119))))) (Val #false))
-  (Let "$r2" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))
-  (Let "$r3" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res3") (Var "$r3")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0")))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 42)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 91))))))
-  (Let "$r0" (Val #(W64 0))
-  (Let "$r1" (Val #false)
-  (Let "$r2" (Val #(W64 0))
-  (Let "$r3" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res3") (Var "$r3")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0")))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "phase")) (Val #(W64 2)))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 46)))) (Val #false)) (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (Val #false)))
-  (Let "$r0" (Val #(W64 2))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Val #(W64 0))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doContinue) (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "n") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "phase") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLe go.byte))) (Pair (Val #(W8 48)) (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")))) (App (Val (GoInstruction (GoOp GoLe go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 57)))) (Val #false)))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doContinue) (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "n") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "n")) (Val #(W64 1))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGe go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "n")) (Val #(W64 7)))))
-  (Let "$r0" (Val #(W64 0))
-  (Let "$r1" (Val #false)
-  (Let "$r2" (Val #(W64 0))
-  (Let "$r3" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res3") (Var "$r3")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0")))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "phase")) (Val #(W64 0)))))
-  (Let "$r0" (Val #(W64 1))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Val #(W64 1))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doContinue) (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "n") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "phase") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "phase")) (Val #(W64 0)))) (If (If (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 43)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 45))))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 48))))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 32))))) (Val #false)))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doContinue) (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "phase")) (Val #(W64 0)))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 35)))) (Val #false)))
-  (Let "$r0" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doContinue) (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "sharp") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "c") (Var "$r0")))))))))
-  (Lam BAnon
-  (Val #()))))))))))
-  (Pair (Pair (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res1"))) (App (Val (GoInstruction (GoLoad go.int))) (Var "$res2"))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res3"))))))))))
-
-/-- The helper `visitKind` of the model (not a function of package `fmt`): printValue of x by its kind, without its methods: the model follows it for the integer and string kinds, which read no memory, and is not defined for the others. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func visitKind(x any) {
-	if isStrKind(x) {
-		return
-	}
-	if isIntKind(x) {
-		return
-	}
-	notModelled()
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def visitKind : val :=
-  (LamV "x"
-  (Seq (App (Val exceptionDo)
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doExecute)
-  (App (Val notModelled) (Val #())))))
-  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val isIntKind) (Var "$a0")))
-  (App (Val doReturn)
-  (Val #()))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val isStrKind) (Var "$a0")))
-  (App (Val doReturn)
-  (Val #()))
-  (App (Val doExecute)
-  (Val #()))))))
-  (Val #())))
-
-/-- The helper `callError` of the model (not a function of package `fmt`) calls `e.Error()`, as Go's
-`handleMethods` does. Go calls it under `catchPanic`, which recovers a panic of the method, prints it
-(`%!v(PANIC=Error method: ...)`) and goes on, so that a program catching panics around the print
-does not see it; the model does not follow that and is stuck there (`notModelled`), rather than
-letting the panic reach the caller: less defined than Go, never different
-(`goose/model/fmt/fprintf_alias_test.go`, `TestMethodPanicRecovered`). Goose's translation (by the
-goose of this revision) of
-
-```go
-func callError(e error) {
-	defer func() {
-		if recover() != nil {
-			notModelled()
-		}
-	}()
-	e.Error()
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def callError : val :=
-  (LamV "e"
-  (Seq (App (Val wrapDeferRecover)
-  (Lam "$defer"
-  (Lam "$panic"
-  (Let "e" (App (Val (GoInstruction (GoAlloc go.error))) (Var "e"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doExecute)
-  (App (App (Val (GoInstruction (MethodResolve go.error go!"Error"))) (App (Val (GoInstruction (GoLoad go.error))) (Var "e"))) (Val #())))))
-  (App (Val doExecute)
-  (Let "$f" (Lam BAnon
-  (Seq (App (Val exceptionDo)
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.InterfaceType [])))) (Pair (App (Val recoverPanic)
-  (Var "$panic")) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.InterfaceType [])))) (Val UntypedNil))))))
-  (App (Val doExecute)
-  (App (Val notModelled) (Val #())))
-  (App (Val doExecute)
-  (Val #()))))
-  (Val #())))
-  (App (Val (GoInstruction (GoStore deferType))) (Pair (Var "$defer") (Let "$oldf" (App (Val (GoInstruction (GoLoad deferType))) (Var "$defer"))
-  (Lam BAnon
-  (Seq (App (Var "$f") (Val #()))
-  (App (Var "$oldf") (Val #()))))))))))))))
-  (Val #())))
-
-/-- The helper `callString` of the model (not a function of package `fmt`): `s.String()`, as
-`callError` calls `Error()` (stuck where Go's `catchPanic` recovers a panic of the method). Goose's
-translation (by the goose of this revision) of
-
-```go
-func callString(s interface{ String() string }) {
-	defer func() {
-		if recover() != nil {
-			notModelled()
-		}
-	}()
-	s.String()
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def callString : val :=
-  (LamV "s"
-  (Seq (App (Val wrapDeferRecover)
-  (Lam "$defer"
-  (Lam "$panic"
-  (Let "s" (App (Val (GoInstruction (GoAlloc (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (Var "s"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doExecute)
-  (App (App (Val (GoInstruction (MethodResolve (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))]) go!"String"))) (App (Val (GoInstruction (GoLoad (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (Var "s"))) (Val #())))))
-  (App (Val doExecute)
-  (Let "$f" (Lam BAnon
-  (Seq (App (Val exceptionDo)
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.InterfaceType [])))) (Pair (App (Val recoverPanic)
-  (Var "$panic")) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.InterfaceType [])))) (Val UntypedNil))))))
-  (App (Val doExecute)
-  (App (Val notModelled) (Val #())))
-  (App (Val doExecute)
-  (Val #()))))
-  (Val #())))
-  (App (Val (GoInstruction (GoStore deferType))) (Pair (Var "$defer") (Let "$oldf" (App (Val (GoInstruction (GoLoad deferType))) (Var "$defer"))
-  (Lam BAnon
-  (Seq (App (Var "$f") (Val #()))
-  (App (Var "$oldf") (Val #()))))))))))))))
-  (Val #())))
-
-/-- The helper `visitArg` of the model (not a function of package `fmt`) calls the methods of x that Go's printArg calls under the directive (verb, sharpV), and nothing else, reads the bytes of a `[]byte` (Go's `fmtBytes`, under every verb but `%T` and `%p`, as printArg's type switch takes it before handleMethods), and reads the elements of a `[]string` (Go's `printValue`, under every verb but `%T` and `%p`: neither a `[]string` nor a `string` has a method for `handleMethods` to call; under a verb that is bad for a string, or `%w`, Go's `badVerb` prints by `printValue` too); the output is not modelled. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func visitArg(x any, verb byte, sharpV bool, wrapErrs bool) {
-	if x == nil {
-		return
-	}
-	if verb == 'T' || verb == 'p' {
-		return
-	}
-	if isBasic(x) {
-		return
-	}
-	if b, ok := x.([]byte); ok {
-		_ = string(b) // printArg's fmtBytes: reads b, calls no method, under every verb
-		return
-	}
-	if ss, ok := x.([]string); ok {
-		_ = joinStrings(ss) // printValue: reads the elements, calls no method, under every verb
-		return
-	}
-	if verb == 'w' {
-		if _, ok := x.(error); !ok || !wrapErrs {
-			visitKind(x)
-			return
-		}
-		verb = 'v'
-	}
-	if _, ok := x.(interface{ Format(State, rune) }); ok {
-		notModelled()
-	}
-	if sharpV {
-		if _, ok := x.(interface{ GoString() string }); ok {
-			notModelled()
-		}
-	} else if verb == 'v' || verb == 's' || verb == 'x' || verb == 'X' || verb == 'q' {
-		if e, ok := x.(error); ok {
-			callError(e)
-			return
-		}
-		if s, ok := x.(interface{ String() string }); ok {
-			if _, ok := x.(interface{ CanInterface() bool }); ok {
-				notModelled() // a reflect.Value, which printArg unwraps
-			}
-			callString(s)
-			return
-		}
-	}
-	visitKind(x)
-}
-```
-
-with these edits: the scratch package's `State.ty` replaced by `go.GoType.Named go!"fmt.State" []` (`fmt.State.ty`); goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def visitArg : val :=
-  (LamV "x"
-  (Lam "verb"
-  (Lam "sharpV"
-  (Lam "wrapErrs"
-  (Seq (App (Val exceptionDo)
-  (Let "wrapErrs" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "wrapErrs"))
-  (Let "sharpV" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "sharpV"))
-  (Let "verb" (App (Val (GoInstruction (GoAlloc go.byte))) (Var "verb"))
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doExecute)
-  (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val visitKind) (Var "$a0"))))))
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "sharpV"))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"GoString" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (Val doExecute)
-  (App (Val notModelled) (Val #())))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0")))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (If (If (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 118)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 115))))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 120))))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 88))))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 113))))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "s" (App (Val (GoInstruction (GoAlloc (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoZeroVal (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (Var "s"))
-  (App (Val callString) (Var "$a0")))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"CanInterface" (go.signature.Signature [] false [go.bool]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (Val doExecute)
-  (App (Val notModelled) (Val #())))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0"))))))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (Pair (Var "s") (Var "$r0"))))))))))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "e" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (Let "$a0" (App (Val (GoInstruction (GoLoad go.error))) (Var "e"))
-  (App (Val callError) (Var "$a0")))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "e") (Var "$r0")))))))))))))
-  (App (Val doExecute)
-  (Val #())))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"Format" (go.signature.Signature [(go.GoType.Named go!"fmt.State" []), go.rune] false []))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (Val doExecute)
-  (App (Val notModelled) (Val #())))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0"))))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 119)))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Val #(W8 118))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "verb") (Var "$r0")))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))) (Val #true) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "wrapErrs"))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val visitKind) (Var "$a0")))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (Var "$r0"))))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.SliceType go.string)))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "ss" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.string)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.string)))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "ss"))
-  (App (Val joinStrings) (Var "$a0")))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (Var "$r0"))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.string)))) (Pair (Var "ss") (Var "$r0")))))))))))))))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b")))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (Var "$r0"))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "b") (Var "$r0")))))))))))))))
-  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (App (Val isBasic) (Var "$a0")))
-  (App (Val doReturn)
-  (Val #()))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 84)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 112))))))
-  (App (Val doReturn)
-  (Val #()))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.any))) (Pair (App (Val (GoInstruction (GoLoad go.any))) (Var "x")) (App (Val (GoInstruction (Convert go.untypedNil go.any))) (Val UntypedNil)))))
-  (App (Val doReturn)
-  (Val #()))
-  (App (Val doExecute)
-  (Val #())))))))))
-  (Val #()))))))
-
-/-- The helper `visitRest` of the model (not a function of package `fmt`) goes through the directives of format from index i, the arguments from argNum, calling what Go calls of each argument (visitArg), and then of each argument left over (Go's %!(EXTRA ...), under %v). It returns the indices of the arguments of the %w directives, and whether it gave up at a directive the model does not follow, every argument being inert. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func visitRest(format string, i int, a []any, argNum int, wrapErrs bool) ([]int, bool) {
-	var wrapped []int
-	for i < len(format) {
-		if format[i] != '%' {
-			i++
-			continue
-		}
-		verb, sharpV, next, ok := parseDirective(format, i+1)
-		if !ok {
-			if allInert(a) {
-				return wrapped, true
-			}
-			notModelled()
-		}
-		i = next
-		if verb < 0 || verb == '%' {
-			continue
-		}
-		if argNum >= len(a) {
-			continue
-		}
-		if verb == 'w' {
-			wrapped = append(wrapped, argNum)
-		}
-		visitArg(a[argNum], byte(verb), sharpV, wrapErrs)
-		argNum++
-	}
-	for argNum < len(a) {
-		visitArg(a[argNum], 'v', false, wrapErrs)
-		argNum++
-	}
-	return wrapped, false
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def visitRest : val :=
-  (LamV "format"
-  (Lam "i"
-  (Lam "a"
-  (Lam "argNum"
-  (Lam "wrapErrs"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.int)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.int)))) (Val #())))
-  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "wrapErrs" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "wrapErrs"))
-  (Let "argNum" (App (Val (GoInstruction (GoAlloc go.int))) (Var "argNum"))
-  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
-  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (Var "i"))
-  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
-  (Let "wrapped" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.int)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.int)))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
-  (Let "$r1" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "$res0") (Var "$r0")))))))))
-  (App (App (App (Val doFor) (Lam BAnon
-  (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.any)]))) (Val #())) (Var "$a0"))))))) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "argNum") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Val #(W64 1)))))))))
-  (App (Val doExecute)
-  (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")))))
-  (Let "$a1" (Val #(W8 118))
-  (Let "$a2" (Val #false)
-  (Let "$a3" (App (Val (GoInstruction (GoLoad go.bool))) (Var "wrapErrs"))
-  (App (App (App (App (Val visitArg) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3"))))))))))
-  (Lam BAnon
-  (Val #()))))))
-  (App (App (App (Val doFor) (Lam BAnon
-  (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))))) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (Let "$a1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))
-  (App (App (Val parseDirective) (Var "$a0")) (Var "$a1"))))
-  (Let "$ret0" (Fst (Fst (Fst (Var "__p"))))
-  (Let "$ret1" (Snd (Fst (Fst (Var "__p"))))
-  (Let "$ret2" (Snd (Fst (Var "__p")))
-  (Let "$ret3" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "$r2" (Var "$ret2")
-  (Let "$r3" (Var "$ret3")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "next" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (Let "sharpV" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "verb" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int))) (Var "next"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "argNum") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Val #(W64 1)))))))))
-  (App (Val doExecute)
-  (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")))))
-  (Let "$a1" (App (Val (GoInstruction (Convert go.int go.byte))) (App (Val (GoInstruction (GoLoad go.int))) (Var "verb")))
-  (Let "$a2" (App (Val (GoInstruction (GoLoad go.bool))) (Var "sharpV"))
-  (Let "$a3" (App (Val (GoInstruction (GoLoad go.bool))) (Var "wrapErrs"))
-  (App (App (App (App (Val visitArg) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3"))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "verb")) (Val #(W64 119)))))
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
-  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum"))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int)))) (LiteralValue [(KeyedElement none (ElementExpression go.int (Var "$sl0")))])))
-  (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType go.int)]))) (Val #())) (Var "$a0")) (Var "$a1"))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "wrapped") (Var "$r0")))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGe go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.any)]))) (Val #())) (Var "$a0"))))))
-  (App (Val doContinue) (Val #()))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "verb")) (Val #(W64 0)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "verb")) (Val #(W64 37))))))
-  (App (Val doContinue) (Val #()))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (Var "$r0"))))))))
-  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok")))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doExecute)
-  (App (Val notModelled) (Val #())))))
-  (If (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
-  (App (Val allInert) (Var "$a0")))
-  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
-  (Let "$r1" (Val #true)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "$res0") (Var "$r0")))))))
-  (App (Val doExecute)
-  (Val #()))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r3")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "next") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "sharpV") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "verb") (Var "$r0"))))))))))))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "i")))) (Val #(W8 37))))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doContinue) (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (Lam BAnon
-  (Val #())))))))))))
-  (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res1")))))))))))
-
-/-- The helper `doPrintf` of the model (not a function of package `fmt`): the formatted string, the indices of the arguments of the %w directives, and whether those are unknown (visitRest gave up). It formats the directives of inert arguments that `formatArg` formats (and the directives of a `[]byte` or a `[]string` that `formatSlice` formats), up to the first directive it does not format or whose argument is not inert; from there the output is arbitrary, and visitRest makes the calls Go makes.
-The model formats `%%`, and `%s`/`%v` of a string, `%d`, `%v`,
-`%0Nd` and `%x` of an integer, of inert arguments, and `%s`, `%v`, `%d`, `%x`, `%X` of a `[]byte` (`%q` of one
-of ASCII bytes) exactly, up to the first other directive; from
-there the output is an arbitrary string, and the model calls each later argument's `Error()` or
-`String()` where Go's formatting does (`visitRest`). It follows Go for the arguments the specs admit
-(`fmt.argsOk`, `Perennial/Proof/fmt/Args.lean`) and is stuck (`notModelled`) for the others it
-cannot tell apart from them: a `Format` method, `%#v` of a `GoString` method, a `reflect.Value`
-under a method verb (Go's `printArg` unwraps it), reflection into a
-value of another kind than an integer or a string (a struct, a pointer under `%v`, a slice other than
-a `[]byte`, a map),
-`%w` of an error when `wrapErrs` is false. Where Go recovers a panic of an argument's method (`catchPanic`),
-the model is stuck (`callError`, `callString`: less defined). `%p` of a pointer, func, map, chan or slice is an arbitrary
-string, without reading memory, as Go's `fmtPointer` prints the address; `%p` of a value of another
-kind is an arbitrary string too, where Go prints it by reflection (`badVerb`) with no method call
-but reading the memory it reaches: the specs admit under `%p` only arguments of those kinds and
-inert ones. `goose/model/fmt/model_diff_test.go` checks the model (the Go below and the helpers')
-against Go's `fmt` on 70 formats and 600 argument lists: the output (each arbitrary string standing
-for any string), the methods called and their order.
-
-Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func doPrintf(format string, a []any, wrapErrs bool) (string, []int, bool) {
-	var out string
-	var argNum int
-	var i int
-	for i < len(format) {
-		if format[i] != '%' {
-			out += string([]byte{format[i]})
-			i++
-			continue
-		}
-		if i+1 < len(format) && format[i+1] == '%' {
-			out += "%"
-			i += 2
-			continue
-		}
-		if argNum < len(a) {
-			s, next, ok := formatSlice(format, i, a[argNum])
-			if ok {
-				out += s
-				argNum++
-				i = next
-				continue
-			}
-		}
-		if argNum < len(a) && inert(a[argNum]) {
-			s, next, ok := formatArg(format, i, a[argNum])
-			if ok {
-				out += s
-				argNum++
-				i = next
-				continue
-			}
-		}
-		wrapped, unknown := visitRest(format, i, a, argNum, wrapErrs)
-		return out + arbitraryString(), wrapped, unknown
-	}
-	if argNum < len(a) {
-		wrapped, unknown := visitRest(format, i, a, argNum, wrapErrs)
-		return out + arbitraryString(), wrapped, unknown
-	}
-	return out, nil, false
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def doPrintf : val :=
-  (LamV "format"
-  (Lam "a"
-  (Lam "wrapErrs"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (Let "$res1" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.int)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.int)))) (Val #())))
-  (Let "$res2" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "wrapErrs" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "wrapErrs"))
-  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
-  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
-  (Let "out" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (Let "argNum" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "out"))
-  (Let "$r1" (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.SliceType go.int)))) (Val UntypedNil))
-  (Let "$r2" (Val #false)
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.any)]))) (Val #())) (Var "$a0"))))))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (Let "$a1" (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))
-  (Let "$a2" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
-  (Let "$a3" (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum"))
-  (Let "$a4" (App (Val (GoInstruction (GoLoad go.bool))) (Var "wrapErrs"))
-  (App (App (App (App (App (Val visitRest) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")))))))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "unknown" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "wrapped" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.int)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.int)))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val arbitraryString) (Val #()))))
-  (Let "$r1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
-  (Let "$r2" (App (Val (GoInstruction (GoLoad go.bool))) (Var "unknown"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "unknown") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "wrapped") (Var "$r0"))))))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (App (App (Val doFor) (Lam BAnon
-  (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))))) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (Let "$a1" (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))
-  (Let "$a2" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
-  (Let "$a3" (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum"))
-  (Let "$a4" (App (Val (GoInstruction (GoLoad go.bool))) (Var "wrapErrs"))
-  (App (App (App (App (App (Val visitRest) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")))))))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "unknown" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "wrapped" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.int)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.int)))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val arbitraryString) (Val #()))))
-  (Let "$r1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
-  (Let "$r2" (App (Val (GoInstruction (GoLoad go.bool))) (Var "unknown"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "unknown") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "wrapped") (Var "$r0"))))))))))))))
-  (If (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.any)]))) (Val #())) (Var "$a0"))))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")))))
-  (App (Val inert) (Var "$a0"))) (Val #false))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (Let "$a1" (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))
-  (Let "$a2" (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")))))
-  (App (App (App (Val formatArg) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
-  (Let "$ret0" (Fst (Fst (Var "__p")))
-  (Let "$ret1" (Snd (Fst (Var "__p")))
-  (Let "$ret2" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "$r2" (Var "$ret2")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "next" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int))) (Var "next"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doContinue) (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "argNum") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Val #(W64 1))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "next") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.any)]))) (Val #())) (Var "$a0"))))))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (Let "$a1" (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))
-  (Let "$a2" (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")))))
-  (App (App (App (Val formatSlice) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
-  (Let "$ret0" (Fst (Fst (Var "__p")))
-  (Let "$ret1" (Snd (Fst (Var "__p")))
-  (Let "$ret2" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "$r2" (Var "$ret2")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "next" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int))) (Var "next"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doContinue) (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "argNum") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Val #(W64 1))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))))))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "next") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0")))))))))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 37)))) (Val #false)))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doContinue) (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Val #(go!"%"))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "i")))) (Val #(W8 37))))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doContinue) (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0")))]))))))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (Lam BAnon
-  (Val #())))))))))))
-  (Pair (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")) (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "$res1"))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res2"))))))))))
+Trusted code for the Go `fmt` package, in namespace `fmt` (as the generated package): the two
+primitive stubs of its Go model (`goose/model/overlay/fmt/print.go`, `Perennial/Code/fmt.toml`) and
+`Printf` (as on lean: its write to standard output is not modelled). Everything else of `fmt` is
+goose's translation: the real print path, and the models of `errorf`, `Fprintf`, `pp.doPrint` and
+`printfFormat` (`Printf`'s formatting) with their model printer.
+-/
+module
+
+public import Perennial.Golang.Defn
+public import Perennial.Code.errors
+public import Perennial.TrustedCode.arbitraryString
+
+@[expose] public section
+
+set_option linter.iris.style.nameCheck false
+
+namespace Perennial
 
-/-- `Printf(format, a...)`: formats with `doPrintf`, calling what Go's formatting
-calls of the arguments, and returns an arbitrary count and either `nil` or an arbitrary error: writing
-to standard output is not modelled (Go returns the count of bytes written and the error of the
-write).
-Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
+namespace fmt
+section code
+variable [GooseExts] [GoGlobalContext]
+
+/-- `underlyingAs[T](x)`: `x`'s value as a `T` and `true` if `x`'s dynamic type has `T`'s
+underlying type, else `T`'s zero value and `false` (also for a `nil` `x`), which plain Go cannot
+test without reflection (the Go body: `reflect.ValueOf(x)` at `T`'s kind, converted to `T`). The
+instruction `TypeAssertUnderlying2 T` (`InterfaceSemantics.type_assert_underlying2_step`), which
+steps for the integer types and `string`, the `T`s the model printer asks; at any other `T` it is
+stuck, less defined than Go. -/
+def underlyingAs.impl (T : go.GoType) : val :=
+  (LamV "x" (App (Val (GoInstruction (TypeAssertUnderlying2 T))) (Var "x")))
+
+/-- `kindIs[T](x)`: whether `x`'s dynamic type has `T`'s underlying type: the second result of
+`TypeAssertUnderlying2 T` (`underlyingAs[T]`'s second result, which the Go body returns). A stub
+rather than a translation of that body, which binds `underlyingAs`'s first result, the value `x`
+holds: the logic cannot step past binding an arbitrary interface's value (it may be a panic value
+as far as the logic knows), and `isIntKind`/`isStrKind` ask `kindIs` of any argument. Stuck at a
+`T` other than the integer types and `string`, as `underlyingAs`. -/
+def kindIs.impl (T : go.GoType) : val :=
+  (LamV "y" (Snd (App (Val (GoInstruction (TypeAssertUnderlying2 T))) (Var "y"))))
+
+/-- `Printf(format, a...)`: formats with the model's `printfFormat` (the printer, the model
+printer's `doPrintf` and `p.free()` of Go's `Fprintf(os.Stdout, format, a...)`, without the write;
+`goose/model/overlay/fmt/print.go`), calling what Go's formatting calls of the arguments, and returns
+an arbitrary count and either `nil` or an arbitrary error: writing to standard output is not
+modelled (Go returns the count of bytes written and the error of the write; translating the write
+needs a semantics primitive for an arbitrary interface value, its error). Lean's trusted `Printf`
+with its call `doPrintf(format, a, false)` of the former hand-written model printer replaced by
+`printfFormat(format, a)`. Goose's translation (by the goose of this revision, with its function
+results in cells `$resI`) of
 
 ```go
 func Printf(format string, a ...any) (int, error) {
-	doPrintf(format, a, false)
+	printfFormat(format, a)
 	n := int(arbitrary())
 	if arbitrary() == 0 {
 		return n, nil
@@ -3586,7 +60,10 @@ func Printf(format string, a ...any) (int, error) {
 }
 ```
 
-with these edits: the call `arbitrary()` replaced by `ArbitraryInt` (as in `arbitraryString`); goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
+with these edits: the call `arbitrary()` replaced by `ArbitraryInt` (as in `arbitraryString`);
+goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`; the name
+`printfFormat`, defined in `Perennial/Code/fmt.lean` (which imports this file), written out as
+`go!"fmt.printfFormat"`. -/
 noncomputable def Printf.impl : val :=
   (LamV "format"
   (Lam "a"
@@ -3629,485 +106,9 @@ noncomputable def Printf.impl : val :=
   (App (Val doExecute)
   (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
   (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
-  (Let "$a2" (Val #false)
-  (App (App (App (Val doPrintf) (Var "$a0")) (Var "$a1")) (Var "$a2"))))))))))
-  (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.error))) (Var "$res1"))))))))
-
-/-- Stores an arbitrary byte in each element of the `[]byte` `s` (a helper of `printerBuf`, not a
-function of package `fmt`), first to last: `s[0]`, then the rest `s[1:]`. -/
-noncomputable def fillArbitraryBytes : val :=
-  rec: "loop" "s" :=
-    if: #(W64 0) <⟨go.int⟩ FuncResolve go.len [go.SliceType go.byte] #() "s" then
-      IndexRef (go.SliceType go.byte) ("s", #(W64 0))
-        <-[go.byte] Convert go.uint64 go.byte ArbitraryInt ;;
-      "loop" (Slice (go.SliceType go.byte)
-        ("s", #(W64 1), FuncResolve go.len [go.SliceType go.byte] #() "s"))
-    else #()
-
-/-- A new `[]byte` of length `n` and arbitrary capacity (`slice._new_cap`), or, when `n` is 0,
-possibly `nil` (a helper of `printerBuf`, not a function of package `fmt`): a fresh printer's `buf`
-is `nil`, and `pp.free` drops a buffer above 64 KiB (`p.buf = nil`), so Go's `Fprintf` can hand
-`Write` a `nil` slice when the output is empty. -/
-noncomputable def printerAlloc : val :=
-  λ: "n",
-    if: ("n" =⟨go.int⟩ #(W64 0)) && (ArbitraryInt =⟨go.uint64⟩ #(W64 0)) then #slice.nil
-    else FuncResolve go.make3 [go.SliceType go.byte] #() "n" (slice._new_cap "n")
-
-/-- The model's stand-in for the printer's buffer `p.buf` that Go's `Fprintf` hands `Write` (a
-primitive of the model, not a function of package `fmt`; in the Go the docstrings quote, a call
-`printerBuf(s)`): the bytes of `s` in a new slice of arbitrary capacity (`slice._new_cap`, as
-`append`'s new capacity) whose spare capacity holds arbitrary bytes, or, for an empty `s`, possibly
-`nil` (`printerAlloc`). Go's buffer comes from a
-`sync.Pool` and holds, past its length, what earlier prints wrote there
-(`goose/model/fmt/fprintf_alias_test.go`); the model's arbitrary bytes include that. -/
-noncomputable def printerBuf : val :=
-  λ: "s",
-    let: "src" := Convert go.string (go.SliceType go.byte) "s" in
-    let: "n" := FuncResolve go.len [go.SliceType go.byte] #() "src" in
-    let: "b" := printerAlloc "n" in
-    fillArbitraryBytes (Slice (go.SliceType go.byte)
-      ("b", "n", FuncResolve go.cap [go.SliceType go.byte] #() "b")) ;;
-    FuncResolve go.copy [go.SliceType go.byte] #() "b" "src" ;;
-    "b"
-
-/-- Begins a write on each element of the `[]byte` `s`, and never finishes it (a helper of
-`retire`, not a function of package `fmt`): `PrepareWrite` with no `FinishStore`, so that any later
-load or store of those bytes is stuck. -/
-noncomputable def retireLoop : val :=
-  rec: "loop" "s" :=
-    if: #(W64 0) <⟨go.int⟩ FuncResolve go.len [go.SliceType go.byte] #() "s" then
-      PrepareWrite (IndexRef (go.SliceType go.byte) ("s", #(W64 0))) ;;
-      "loop" (Slice (go.SliceType go.byte)
-        ("s", #(W64 1), FuncResolve go.len [go.SliceType go.byte] #() "s"))
-    else #()
-
-/-- The model's stand-in for the printer's buffer going back to its `sync.Pool` after `Write`
-returns (a primitive of the model, not a function of package `fmt`; in the Go the docstrings quote,
-a call `retire(b)`): every element of `b` up to its capacity is left with a write begun and never
-finished (`retireLoop`), so that any later access through a slice that `Write` kept is stuck. In Go
-the buffer goes back to the pool and later prints overwrite those bytes, unless it is above 64 KiB,
-which `pp.free` drops (then a kept slice stays intact in Go): the model is less defined than Go in
-both cases (`goose/model/fmt/fprintf_alias_test.go`). -/
-noncomputable def retire : val :=
-  λ: "b",
-    retireLoop "b" ;;
-    retireLoop (Slice (go.SliceType go.byte)
-      ("b", FuncResolve go.len [go.SliceType go.byte] #() "b",
-        FuncResolve go.cap [go.SliceType go.byte] #() "b"))
-
-/-- `Fprintf(w, format, a...)`: formats with `doPrintf` (with `wrapErrs` false), calling
-what Go's formatting calls of the arguments, then calls `w.Write` once with the formatted bytes (also
-when they are empty), and returns what `Write` returns. Go's (`fmt/print.go`)
-
-```go
-func Fprintf(w io.Writer, format string, a ...any) (n int, err error) {
-	p := newPrinter()
-	p.doPrintf(format, a)
-	n, err = w.Write(p.buf)
-	p.free()
-	return
-}
-```
-
-hands `Write` its printer's buffer `p.buf`, which comes from a `sync.Pool` and goes back to it: its
-spare capacity holds what earlier prints wrote there, and a later print overwrites its bytes (a buffer
-above 64 KiB is dropped instead, `p.buf = nil`, and never reused, so that the next printer's may be
-`nil`). The model hands `Write` the formatted bytes in a slice whose spare capacity holds arbitrary
-bytes, possibly `nil` when they are empty (`printerBuf`), which includes gc's slices, and after `Write` returns leaves every element of that slice, up to its
-capacity, with a write begun and never finished (`retire`), so that a writer that keeps the slice
-(which `io.Writer` forbids: "Implementations must not retain p") is stuck when it later uses it: less
-defined than Go there, never different (`goose/model/fmt/fprintf_alias_test.go`). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func Fprintf(w io.Writer, format string, a ...any) (int, error) {
-	s, _, _ := doPrintf(format, a, false)
-	b := printerBuf(s)
-	n, err := w.Write(b)
-	retire(b)
-	return n, err
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def Fprintf.impl : val :=
-  (LamV "w"
-  (Lam "format"
-  (Lam "a"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
-  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
-  (Let "w" (App (Val (GoInstruction (GoAlloc _root_.Perennial.io.Writer.ty))) (Var "w"))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
-  (Let "$a2" (Val #false)
-  (App (App (App (Val doPrintf) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
-  (Let "$ret0" (Fst (Fst (Var "__p")))
-  (Let "$ret1" (Snd (Fst (Var "__p")))
-  (Let "$ret2" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "$r2" (Var "$ret2")
-  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
-  (App (Val printerBuf) (Var "$a0")))
-  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
-  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.io.Writer.ty go!"Write"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.io.Writer.ty))) (Var "w"))) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
-  (Let "n" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int))) (Var "n"))
-  (Let "$r1" (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0")))))))))
-  (App (Val doExecute)
-  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
-  (App (Val retire) (Var "$a0")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "n") (Var "$r0"))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "b") (Var "$r0")))))))))
-  (App (Val doExecute)
-  (Var "$r2")))))
-  (App (Val doExecute)
-  (Var "$r1")))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0")))))))))))))))))
-  (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.error))) (Var "$res1")))))))))
-
-/-- `Errorf(format, a...)`: formats with `doPrintf` (with `wrapErrs` true: a `%w`
-of an error is formatted as `%v`, Go's `handleMethods`), then returns what Go's `errorf` returns
-(`fmt/errors.go`): `errors.New(s)` when no `%w` directive had an argument, a `*wrapError` holding the
-argument as an `error` (`nil` if it is not one) when one had, a `*wrapErrors` holding those of the
-arguments that are errors when several had (Go sorts and deduplicates them only after an argument
-index, which the model does not follow). Go's shortcut for no argument and no `%` returns
-`errors.New(format)`, the same error as this. Where `visitRest` gave up on a directive it does not
-follow, every argument being inert (none is an error), the error is any of the three, holding no
-error. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func Errorf(format string, a ...any) error {
-	s, wrapped, unknown := doPrintf(format, a, true)
-	if unknown {
-		n := arbitrary()
-		if n == 0 {
-			return errors.New(s)
-		}
-		if n == 1 {
-			return &wrapError{msg: s}
-		}
-		return &wrapErrors{msg: s}
-	}
-	if len(wrapped) == 0 {
-		return errors.New(s)
-	}
-	if len(wrapped) == 1 {
-		w := &wrapError{msg: s}
-		w.err, _ = a[wrapped[0]].(error)
-		return w
-	}
-	var errs []error
-	for _, argNum := range wrapped {
-		if e, ok := a[argNum].(error); ok {
-			errs = append(errs, e)
-		}
-	}
-	return &wrapErrors{s, errs}
-}
-```
-
-with these edits: the call `arbitrary()` replaced by `ArbitraryInt` (as in `arbitraryString`); goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`; the scratch package's `wrapError.ty` replaced by `go.GoType.Named go!"fmt.wrapError" []` (`fmt.wrapError.ty`, whose methods are translated); the scratch package's `wrapErrors.ty` replaced by `go.GoType.Named go!"fmt.wrapErrors" []` (`fmt.wrapErrors.ty`). -/
-noncomputable def Errorf.impl : val :=
-  (LamV "format"
-  (Lam "a"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
-  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
-  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
-  (Let "$a2" (Val #true)
-  (App (App (App (Val doPrintf) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
-  (Let "$ret0" (Fst (Fst (Var "__p")))
-  (Let "$ret1" (Snd (Fst (Var "__p")))
-  (Let "$ret2" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "$r2" (Var "$ret2")
-  (Let "unknown" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "wrapped" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.int)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.int)))) (Val #())))
-  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "errs" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.error)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.error)))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapErrors" [])) go.error))) (App (Val (GoInstruction (GoAlloc (go.GoType.Named go!"fmt.wrapErrors" [])))) (Let "$v0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
-  (Let "$v1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.error)))) (Var "errs"))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.Named go!"fmt.wrapErrors" [])))) (LiteralValue [(KeyedElement none (ElementExpression go.string (Var "$v0"))), (KeyedElement none (ElementExpression (go.GoType.SliceType go.error) (Var "$v1")))]))))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
-  (Let "argNum" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (App (App (Val (slice.forRange go.int)) (Var "$range"))
-  (Lam "$key"
-  (Lam "$value"
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum"))))))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
-  (Let "e" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.error)))) (Var "errs"))
-  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (GoLoad go.error))) (Var "e"))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.error)))) (LiteralValue [(KeyedElement none (ElementExpression go.error (Var "$sl0")))])))
-  (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType go.error)]))) (Val #())) (Var "$a0")) (Var "$a1"))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.error)))) (Pair (Var "errs") (Var "$r0")))))
-  (App (Val doExecute)
-  (Val #())))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "e") (Var "$r0"))))))))))))))
-  (App (Val doExecute)
-  (Var "$key")))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "argNum") (Var "$value"))))))))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.int)]))) (Val #())) (Var "$a0"))) (Val #(W64 1)))))
-  (Let "$r0" (App (Val (GoInstruction (GoAlloc (go.GoType.Named go!"fmt.wrapError" [])))) (Let "$v0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.Named go!"fmt.wrapError" [])))) (LiteralValue [(KeyedElement (some (KeyField go!"msg")) (ElementExpression go.string (Var "$v0")))]))))
-  (Let "w" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" []))))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" []))))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$l0" (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"fmt.wrapError" []) go!"err"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" []))))) (Var "w")))
-  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.int)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped")) (Val #(W64 0)))))))))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" [])) go.error))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" []))))) (Var "w")))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (Val doExecute)
-  (Var "$r1")))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$l0") (Var "$r0")))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" []))))) (Pair (Var "w") (Var "$r0")))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
-  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.int)]))) (Val #())) (Var "$a0"))) (Val #(W64 0)))))
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
-  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.errors.New []))) (Val #())) (Var "$a0")))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "unknown"))
-  (Let "$r0" ArbitraryInt
-  (Let "n" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapErrors" [])) go.error))) (App (Val (GoInstruction (GoAlloc (go.GoType.Named go!"fmt.wrapErrors" [])))) (Let "$v0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.Named go!"fmt.wrapErrors" [])))) (LiteralValue [(KeyedElement (some (KeyField go!"msg")) (ElementExpression go.string (Var "$v0")))])))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "n")) (Val #(W64 1)))))
-  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" [])) go.error))) (App (Val (GoInstruction (GoAlloc (go.GoType.Named go!"fmt.wrapError" [])))) (Let "$v0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.Named go!"fmt.wrapError" [])))) (LiteralValue [(KeyedElement (some (KeyField go!"msg")) (ElementExpression go.string (Var "$v0")))])))))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "n")) (Val #(W64 0)))))
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
-  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.errors.New []))) (Val #())) (Var "$a0")))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "n") (Var "$r0")))))))
-  (App (Val doExecute)
-  (Val #()))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "unknown") (Var "$r2")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "wrapped") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0"))))))))))))))))))
-  (App (Val (GoInstruction (GoLoad go.error))) (Var "$res0"))))))
-
-
-/-- `Fprint(w, a...)`: calls what Go's formatting calls of each operand (`visitArg` under `%v`,
-without `#`), then calls `w.Write` once with an arbitrary string's bytes (also when it is empty),
-and returns what `Write` returns. Go's (`fmt/print.go`)
-
-```go
-func Fprint(w io.Writer, a ...any) (n int, err error) {
-	p := newPrinter()
-	p.doPrint(a)
-	n, err = w.Write(p.buf)
-	p.free()
-	return
-}
-
-func (p *pp) doPrint(a []any) {
-	prevString := false
-	for argNum, arg := range a {
-		isString := arg != nil && reflect.TypeOf(arg).Kind() == reflect.String
-		// Add a space between two non-string arguments.
-		if argNum > 0 && !isString && !prevString {
-			p.buf.writeByte(' ')
-		}
-		p.printArg(arg, 'v')
-		prevString = isString
-	}
-}
-```
-
-prints each operand by `printArg` under `%v` (`p.fmt` is cleared: no flags, width or precision), in
-order, with a space between two operands neither of which is a string (by kind: reading the type
-only); the only calls into the operands are `printArg`'s, which `visitArg` makes (the model is stuck
-where it does not follow them: a `Format` method, a `reflect.Value`, printing by reflection beyond the
-integer and string kinds). The output is not modelled: an arbitrary string, which includes Go's.
-`Write` gets it as `Fprintf`'s gets its output (`printerBuf`, then `retire`; the same evidence,
-`goose/model/fmt/fprintf_alias_test.go`, as `Fprint` uses the same pooled printer). Goose's
-translation (by the goose of this revision, with its function results in cells `$resI`) of
-
-```go
-func Fprint(w io.Writer, a ...any) (int, error) {
-	for _, x := range a {
-		visitArg(x, 'v', false, false)
-	}
-	b := printerBuf(arbitraryString())
-	n, err := w.Write(b)
-	retire(b)
-	return n, err
-}
-```
-
-with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
-noncomputable def Fprint.impl : val :=
-  (LamV "w"
-  (Lam "a"
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
-  (Let "w" (App (Val (GoInstruction (GoAlloc _root_.Perennial.io.Writer.ty))) (Var "w"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (Let "$a0" (App (Val arbitraryString) (Val #()))
-  (App (Val printerBuf) (Var "$a0")))
-  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
-  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.io.Writer.ty go!"Write"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.io.Writer.ty))) (Var "w"))) (Var "$a0")))
-  (Let "$ret0" (Fst (Var "__p"))
-  (Let "$ret1" (Snd (Var "__p"))
-  (Let "$r0" (Var "$ret0")
-  (Let "$r1" (Var "$ret1")
-  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
-  (Let "n" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int))) (Var "n"))
-  (Let "$r1" (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res1") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0")))))))))
-  (App (Val doExecute)
-  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
-  (App (Val retire) (Var "$a0")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "n") (Var "$r0"))))))))))))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "b") (Var "$r0")))))))))
-  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
-  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (App (Val (GoInstruction (GoZeroVal go.any))) (Val #())))
-  (App (App (Val (slice.forRange go.any)) (Var "$range"))
-  (Lam "$key"
-  (Lam "$value"
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doExecute)
-  (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
-  (Let "$a1" (Val #(W8 118))
-  (Let "$a2" (Val #false)
-  (Let "$a3" (Val #false)
-  (App (App (App (App (Val visitArg) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")))))))))
-  (App (Val doExecute)
-  (Var "$key")))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore go.any))) (Pair (Var "x") (Var "$value"))))))))))))))
+  (App (App (App (Val (GoInstruction (FuncResolve go!"fmt.printfFormat" []))) (Val #())) (Var "$a0")) (Var "$a1")))))))))
   (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.error))) (Var "$res1"))))))))
 
-
-/-- `Print(a...)`: not modelled; stuck. (`Print` takes one argument, the slice `a`.) -/
-def Print.impl : val :=
-  λ: "a",
-    Panic "unimplemented"
-
 end code
 end fmt
 
```

### Perennial/TrustedCode/log.lean  (tier 0, trusted-model)

```diff
diff --git a/Perennial/TrustedCode/log.lean b/Perennial/TrustedCode/log.lean
index 119b90ed2..f2ee0e14e 100644
--- a/Perennial/TrustedCode/log.lean
+++ b/Perennial/TrustedCode/log.lean
@@ -1,5 +1,5 @@
 /-
-Trusted definitions of `log`, in namespace `log` like the generated package.
+Trusted definitions of `log`, in namespace `log` like the generated package: `std`'s initializer.
 -/
 module
 
@@ -15,12 +15,6 @@ namespace log
 section code
 variable [GooseExts] [GoGlobalContext]
 
-def Printf.impl : val :=
-  λ: "format" "vs", #()
-
-def Println.impl : val :=
-  λ: "vs", #()
-
 /-- The initializer of `std` (`log/log.go`), the standard logger:
 
 ```go
@@ -35,32 +29,12 @@ output, prefix and flags (`SetOutput` takes the logger's own new mutex): it cann
 has no effect beyond the new logger and the variable. Translating it would need `os.Stderr`,
 whose initializer (`NewFile(uintptr(syscall.Stderr), "/dev/stderr")`) wraps a file
 descriptor; `os` is not translated. The readers of `std` (`Default`, `Print*`, `SetOutput`, ...,
-and the closure that `init` stores) are not translated, and the models of `Printf` and
-`Println` above do not read it; a translated reader could not load the variable (nothing gives
-a points-to for it). -/
+and the closure that `init` stores) are not translated, and the Go models of `Printf` and
+`Println` (`goose/model/overlay/log`) do not read it; a translated reader could not load the
+variable (nothing gives a points-to for it). -/
 def std.init : val :=
   λ: <>, #()
 
-/-- `log`'s `init` function (`log/log.go`):
-
-```go
-func init() {
-	internal.DefaultOutput = func(pc uintptr, data []byte) error {
-		return std.output(pc, 0, func(buf []byte) []byte {
-			return append(buf, data...)
-		})
-	}
-}
-```
-
-The model does nothing. Go's `init` stores a closure into `log/internal.DefaultOutput`, the
-output of `log/slog`'s default handler; it cannot panic. `log/slog` and `log/internal` are not
-translated, so no translated code reads that variable. (goose translates this `init`, but
-its proof cannot be done: the variable belongs to `log/internal`, and a package's `isPkgInit`
-is persistent, so no ownership of another package's variable reaches `log`'s initializer.) -/
-def init.«0».impl : val :=
-  λ: <>, #()
-
 end code
 end log
 
```

### Perennial/TrustedCode/os.lean  (tier 0, trusted-model)

```diff
diff --git a/Perennial/TrustedCode/os.lean b/Perennial/TrustedCode/os.lean
index c72a6931d..da35d0929 100644
--- a/Perennial/TrustedCode/os.lean
+++ b/Perennial/TrustedCode/os.lean
@@ -7,7 +7,7 @@ which are not translated by the user's decision (fix-semantics Case 33).
 module
 
 public import Perennial.Golang.Defn.Pre
-public import Perennial.TrustedCode.syscall
+public import Perennial.Code.internal.gomodel
 
 @[expose] public section
 
@@ -21,10 +21,11 @@ variable [GooseExts] [GoGlobalContext]
 
 /-- `runtime_args() []string` (`proc.go`: `func runtime_args() []string // in package
 runtime`): a `go:linkname` with no Go body; the runtime returns a copy of the command-line
-arguments. The model: an arbitrary `[]string` (`syscall.arbitraryStrings`), which covers every
-argument list. -/
+arguments. The model: an arbitrary `[]string`, a call of `internal/gomodel.ChooseStrings`
+(translated Go over `Choose`, `goose/model/overlay/internal/gomodel/choose.go`), which covers
+every argument list. -/
 noncomputable def runtime_args.impl : val :=
-  syscall.arbitraryStrings
+  λ: <>, FuncResolve internal.gomodel.ChooseStrings [] #() #()
 
 /-- `runtime_beforeExit(exitCode int)` (`proc.go`: `func runtime_beforeExit(exitCode int) // implemented
 in runtime`), which `Exit` (translated) calls before `syscall.Exit`: a `go:linkname` with no Go
```

### Perennial/TrustedCode/syscall.lean  (tier 0, trusted-model)

```diff
diff --git a/Perennial/TrustedCode/syscall.lean b/Perennial/TrustedCode/syscall.lean
index 7cc9dd026..5b6b30ffb 100644
--- a/Perennial/TrustedCode/syscall.lean
+++ b/Perennial/TrustedCode/syscall.lean
@@ -1,12 +1,12 @@
 /-
 Trusted code for the Go `syscall` package, in namespace `syscall` (as the generated package): what
-its initializer runs that has no Go body (`runtime_envs`) or whose effect Perennial does not model
-(`init.0`, the RLIMIT_NOFILE raise), and `Exit`.
+its initializer runs that has no Go body (`runtime_envs`), and `Exit`. (`init.0` is translated, over
+the Go model of the system call `prlimit1`, `goose/model/overlay/syscall`.)
 -/
 module
 
 public import Perennial.Golang.Defn.Pre
-public import Perennial.TrustedCode.arbitraryString
+public import Perennial.Code.internal.gomodel
 
 @[expose] public section
 
@@ -18,76 +18,13 @@ namespace syscall
 section code
 variable [GooseExts] [GoGlobalContext]
 
-/-- An arbitrary `[]string`: the model of a `go:linkname` into the runtime that returns the
-process's strings (`runtime_envs` here, `os.runtime_args`). It is goose's translation of
-
-```go
-func arbitraryStrings() []string {
-	var a []string
-	for arbitrary() != 0 {
-		a = append(a, arbitraryString())
-	}
-	return a
-}
-```
-
-with each call `arbitrary()` replaced by `ArbitraryInt` (an arbitrary `uint64`) and
-`arbitraryString()` by `fmt.arbitraryString` (every string). It can return every slice of
-strings (and may also not terminate, which partial correctness allows). -/
-noncomputable def arbitraryStrings : val :=
-  (LamV BAnon
-  (Let "$res0" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.string)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.string)))) (Val #())))
-  (Seq (App (Val exceptionDo)
-  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.string)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.string)))) (Val #())))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "a"))
-  (App (App (Val exceptionSeq) (Lam BAnon
-  (App (Val doReturn)
-  (Val #()))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.string)))) (Pair (Var "$res0") (Var "$r0"))))))))
-  (App (App (App (Val doFor) (Lam BAnon
-  (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair ArbitraryInt (Val #(W64 0))))))) (Lam BAnon
-  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "a"))
-  (Let "$a1" (Let "$sl0" (App (Val fmt.arbitraryString) (Val #()))
-  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string)))) (LiteralValue [(KeyedElement none (ElementExpression go.string (Var "$sl0")))])))
-  (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType go.string)]))) (Val #())) (Var "$a0")) (Var "$a1"))))
-  (App (Val doExecute)
-  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.string)))) (Pair (Var "a") (Var "$r0")))))))
-  (Lam BAnon
-  (Val #()))))))
-  (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "$res0")))))
-
 /-- `runtime_envs() []string` (`env_unix.go`: `func runtime_envs() []string // in package
 runtime`): a `go:linkname` with no Go body; the runtime returns a copy of the process's
-environment. The model: an arbitrary `[]string` (`arbitraryStrings`), which covers every
-environment. -/
+environment. The model: an arbitrary `[]string`, a call of `internal/gomodel.ChooseStrings`
+(translated Go over `Choose`, `goose/model/overlay/internal/gomodel/choose.go`), which covers
+every environment. -/
 noncomputable def runtime_envs.impl : val :=
-  arbitraryStrings
-
-/-- `syscall`'s `init` function (`rlimit.go`):
-
-```go
-func init() {
-	var lim Rlimit
-	if err := Getrlimit(RLIMIT_NOFILE, &lim); err == nil && lim.Max > 0 && lim.Cur < lim.Max-1 {
-		origRlimitNofile.Store(&lim)
-		nlim := lim
-		nlim.Cur = nlim.Max - 1
-		adjustFileLimit(&nlim)
-		setrlimit(RLIMIT_NOFILE, &nlim)
-	}
-}
-```
-
-It raises the process's soft limit on open files through the raw `prlimit` system call
-(`RawSyscall6`, assembly), and records the original limit in `origRlimitNofile`, which only
-`Setrlimit` and `exec` (`forkExec`, to restore the child's limit) read. It cannot panic. The model
-does nothing: the changed limit and `origRlimitNofile` are observable only through `exec`, a
-`Getrlimit` system call or running out of file descriptors, none of which Perennial models (the
-user's decision, fix-semantics Case 33: "P1: (ii)", 2026-11-04). -/
-def init.«0».impl : val :=
-  λ: <>, #()
+  λ: <>, FuncResolve internal.gomodel.ChooseStrings [] #() #()
 
 /-- `Exit(code int)` (`syscall.go`: `func Exit(code int)`, no Go body; the runtime provides it,
 `runtime.syscall_Exit`, which calls `exit`, the `exit_group` system call): the process ends with
```

### goose/model/fmt/fprintf_alias_test.go  (tier 0, translator)

```diff
diff --git a/goose/model/fmt/fprintf_alias_test.go b/goose/model/fmt/fprintf_alias_test.go
deleted file mode 100644
index d919e0e1f..000000000
--- a/goose/model/fmt/fprintf_alias_test.go
+++ /dev/null
@@ -1,115 +0,0 @@
-package fmt_test
-
-// The evidence for the model of fmt.Fprintf (Perennial/TrustedCode/fmt.lean, Fprintf.impl): gc
-// hands Write its printer's pooled buffer, not a copy of the formatted bytes. Its spare capacity
-// holds what earlier prints left there, and a writer that keeps the slice past the call sees it
-// overwritten by a later print (unless the buffer is above 64 KiB, which pp.free drops, so that the
-// next printer's buffer is nil and Write may get a nil slice). The model hands Write a slice whose spare capacity holds arbitrary
-// bytes (printerBuf), so gc's contents are among the model's outcomes, and after Write returns it
-// leaves every cell of that slice, up to its capacity, with a write begun and never finished
-// (retire), so that any later access through a kept slice is stuck: less defined than Go there,
-// never different.
-
-import (
-	"bytes"
-	"fmt"
-	"strings"
-	"testing"
-)
-
-type peek struct{ spare string }
-
-// Write keeps nothing: during the call, it reads its argument's spare capacity.
-func (k *peek) Write(p []byte) (int, error) {
-	k.spare = string(p[len(p):cap(p)])
-	return len(p), nil
-}
-
-type nop struct{}
-
-func (nop) Write(p []byte) (int, error) { return len(p), nil }
-
-// TestFprintfSpareCapacity: the spare capacity of Write's argument holds an earlier print's
-// bytes, which the model's arbitrary bytes allow.
-func TestFprintfSpareCapacity(t *testing.T) {
-	for try := 0; try < 10; try++ {
-		fmt.Fprintf(nop{}, "secret-%d", 12345)
-		k := &peek{}
-		fmt.Fprintf(k, "hi")
-		if k.spare != string(make([]byte, len(k.spare))) {
-			return // gc's spare capacity is not zero: the model must not zero it
-		}
-	}
-	t.Fatal("the spare capacity of Write's argument was always zero; gc no longer reuses the printer's buffer")
-}
-
-type keep struct{ p []byte }
-
-// Write keeps its argument past the call.
-func (k *keep) Write(p []byte) (int, error) {
-	k.p = p
-	return len(p), nil
-}
-
-// TestFprintfKeptSliceOverwritten: a slice Write kept is overwritten by a later print, where a
-// copy would stay; in the model any access through it is stuck.
-func TestFprintfKeptSliceOverwritten(t *testing.T) {
-	for try := 0; try < 10; try++ {
-		k := &keep{}
-		fmt.Fprintf(k, "first")
-		_ = fmt.Sprintf("second-%d", 99999)
-		if string(k.p) != "first" {
-			return // overwritten by the later Sprintf
-		}
-	}
-	t.Fatal("the kept slice was never overwritten; gc no longer reuses the printer's buffer")
-}
-
-type nilcheck struct{ isNil bool }
-
-func (k *nilcheck) Write(p []byte) (int, error) {
-	k.isNil = p == nil
-	return len(p), nil
-}
-
-// TestFprintfNilBuffer: after a print above 64 KiB (whose buffer pp.free drops), Fprintf with empty
-// output hands Write a nil slice, which the model's printerBuf allows for an empty output.
-func TestFprintfNilBuffer(t *testing.T) {
-	for try := 0; try < 10; try++ {
-		fmt.Fprintf(nop{}, "%s", strings.Repeat("x", 70000))
-		k := &nilcheck{}
-		fmt.Fprintf(k, "")
-		if k.isNil {
-			return
-		}
-	}
-	t.Fatal("Write never got a nil slice; gc no longer drops large printer buffers")
-}
-
-type panickingError struct{}
-
-func (panickingError) Error() string { panic("boom") }
-
-type panickingStringer struct{}
-
-func (panickingStringer) String() string { panic("boom") }
-
-// TestMethodPanicRecovered is the evidence for callError and callString (visitArg): gc's printer
-// recovers a panic of an argument's Error() or String() (catchPanic), prints it, and returns
-// normally, so a program that would catch the panic itself goes on differently. The model is
-// stuck there (notModelled) rather than letting the panic reach the caller.
-func TestMethodPanicRecovered(t *testing.T) {
-	var buf bytes.Buffer
-	n, err := fmt.Fprintf(&buf, "%v %s", panickingError{}, panickingStringer{})
-	if err != nil || n != buf.Len() || !strings.Contains(buf.String(), "PANIC=") {
-		t.Fatalf("Fprintf = %d, %v, %q: gc no longer recovers the method's panic", n, err, buf.String())
-	}
-	for _, arg := range []any{panickingError{}, panickingStringer{}} {
-		if !runModel(func() { modelFprintf(&buf, "%v", arg) }) {
-			t.Fatalf("the model does not get stuck on a panicking method of %T", arg)
-		}
-		if !runModel(func() { modelSprintf("%s", arg) }) {
-			t.Fatalf("the model's Sprintf does not get stuck on a panicking method of %T", arg)
-		}
-	}
-}
```

### goose/model/fmt/method_panic_test.go  (tier 0, translator)

```diff
diff --git a/goose/model/fmt/method_panic_test.go b/goose/model/fmt/method_panic_test.go
new file mode 100644
index 000000000..6d6290b7e
--- /dev/null
+++ b/goose/model/fmt/method_panic_test.go
@@ -0,0 +1,39 @@
+package fmt_test
+
+// The evidence that the model printer's callError and callString (visitArg) may be stuck where an
+// argument's method panics: gc's printer recovers the panic.
+
+import (
+	"bytes"
+	"fmt"
+	"strings"
+	"testing"
+)
+
+type panickingError struct{}
+
+func (panickingError) Error() string { panic("boom") }
+
+type panickingStringer struct{}
+
+func (panickingStringer) String() string { panic("boom") }
+
+// TestMethodPanicRecovered is the evidence for callError and callString (visitArg): gc's printer
+// recovers a panic of an argument's Error() or String() (catchPanic), prints it, and returns
+// normally, so a program that would catch the panic itself goes on differently. The model is
+// stuck there (notModelled) rather than letting the panic reach the caller.
+func TestMethodPanicRecovered(t *testing.T) {
+	var buf bytes.Buffer
+	n, err := fmt.Fprintf(&buf, "%v %s", panickingError{}, panickingStringer{})
+	if err != nil || n != buf.Len() || !strings.Contains(buf.String(), "PANIC=") {
+		t.Fatalf("Fprintf = %d, %v, %q: gc no longer recovers the method's panic", n, err, buf.String())
+	}
+	for _, arg := range []any{panickingError{}, panickingStringer{}} {
+		if !runModel(func() { modelFprintf(&buf, "%v", arg) }) {
+			t.Fatalf("the model does not get stuck on a panicking method of %T", arg)
+		}
+		if !runModel(func() { modelSprintf("%s", arg) }) {
+			t.Fatalf("the model's Sprintf does not get stuck on a panicking method of %T", arg)
+		}
+	}
+}
```

### goose/model/fmt/model_copy_test.go  (tier 0, translator)

```diff
diff --git a/goose/model/fmt/model_copy_test.go b/goose/model/fmt/model_copy_test.go
new file mode 100644
index 000000000..3087aeb35
--- /dev/null
+++ b/goose/model/fmt/model_copy_test.go
@@ -0,0 +1,49 @@
+package fmt_test
+
+// model_test.go is the overlay's model printer (goose/model/overlay/fmt/printmodel.go, package
+// fmt) rewritten into this package, so that the differential tests run the very Go that goose
+// translates: the package clause, the import of internal/gomodel dropped, and each
+// gomodel.ChooseUint64() replaced by arbitrary() and each gomodel.Choose() by arbitraryBool()
+// (model_harness_test.go). TestModelCopy fails when
+// the two differ; go test -run TestModelCopy -update rewrites model_test.go.
+
+import (
+	"flag"
+	"os"
+	"strings"
+	"testing"
+)
+
+var update = flag.Bool("update", false, "rewrite model_test.go from the overlay's printmodel.go")
+
+func modelCopy(src string) string {
+	s := strings.Replace(src, "\npackage fmt\n", "\npackage fmt_test\n", 1)
+	s = strings.Replace(s, "\t\"internal/gomodel\"\n", "", 1)
+	s = strings.ReplaceAll(s, "gomodel.ChooseUint64()", "arbitrary()")
+	s = strings.ReplaceAll(s, "gomodel.Choose()", "arbitraryBool()")
+	return "// Code generated from goose/model/overlay/fmt/printmodel.go by model_copy_test.go; DO NOT EDIT.\n\n" + s
+}
+
+func TestModelCopy(t *testing.T) {
+	src, err := os.ReadFile("../overlay/fmt/printmodel.go")
+	if err != nil {
+		t.Fatal(err)
+	}
+	want := modelCopy(string(src))
+	if strings.Contains(want, "gomodel.") {
+		t.Fatal("printmodel.go calls a gomodel function other than Choose and ChooseUint64: extend modelCopy")
+	}
+	if *update {
+		if err := os.WriteFile("model_test.go", []byte(want), 0o644); err != nil {
+			t.Fatal(err)
+		}
+		return
+	}
+	got, err := os.ReadFile("model_test.go")
+	if err != nil {
+		t.Fatal(err)
+	}
+	if string(got) != want {
+		t.Fatal("model_test.go differs from the overlay's printmodel.go: go test -run TestModelCopy -update")
+	}
+}
```

### goose/model/fmt/model_diff_test.go  (tier 0, translator)

```diff
diff --git a/goose/model/fmt/model_diff_test.go b/goose/model/fmt/model_diff_test.go
index 164499250..9a5af0cea 100644
--- a/goose/model/fmt/model_diff_test.go
+++ b/goose/model/fmt/model_diff_test.go
@@ -1,12 +1,13 @@
 package fmt_test
 
-// Differential tests of the model of fmt (model_test.go, the Go that the docstrings of
-// Perennial/TrustedCode/fmt.lean quote) against Go's fmt: on every call the model does not get
-// stuck on, its output matches Go's (each arbitrary string in it standing for any string), it
-// calls exactly the methods Go calls, in the same order, and its Errorf returns an error of the
-// same kind (errors.New, one wrapped error, several) wrapping the same errors. And on every call
-// the specs admit (argsOk, a transcription of fmt.argsOk of Perennial/Proof/fmt/Base.lean), the
-// model does not get stuck.
+// Differential tests of the Go model of fmt (goose/model/overlay/fmt: the model printer of
+// printmodel.go, copied into model_test.go, and the replaced declarations of print.go, mirrored in
+// model_harness_test.go) against Go's fmt: on every call the model does not get stuck on, its
+// output matches Go's (each arbitrary string in it standing for any string), it calls exactly the
+// methods Go calls, in the same order, and its Errorf returns an error of the same kind
+// (errors.New, one wrapped error, several) wrapping the same errors. And on every call the specs
+// admit (argsOk, a transcription of fmt.argsOk of Perennial/Proof/fmt/Args.lean), the model does
+// not get stuck.
 
 import (
 	"errors"
@@ -374,6 +375,7 @@ func TestModelSprintf(t *testing.T) {
 	t.Logf("%d calls admitted, %d where the model is stuck", admitted, stuckN)
 }
 
+// TestModelPrintf: the formatting of the trusted Printf (printfFormat) calls what Go's Printf calls.
 func TestModelPrintf(t *testing.T) {
 	for _, format := range testFormats {
 		for _, a := range argTuples() {
@@ -381,7 +383,7 @@ func TestModelPrintf(t *testing.T) {
 			_ = fmt.Sprintf(format, a...) // Printf formats as Sprintf does
 			goCalls := calls
 			calls = nil
-			stuck := runModel(func() { modelPrintf(format, a...) })
+			stuck := runModel(func() { modelPrintfFormat(format, a...) })
 			if stuck {
 				continue
 			}
@@ -557,6 +559,62 @@ func TestModelFprint(t *testing.T) {
 	t.Logf("%d operand lists admitted", admitted)
 }
 
+// Fprintln, as Fprint (over pp.doPrintln): the calls Go's printArg makes of each operand under %v,
+// in order, then one Write, returning what Write returns; the output is arbitrary. Admitted (the
+// spec's fmt.printArgOk): each operand as argOkAt admits it under %v.
+func TestModelFprintln(t *testing.T) {
+	werr := errors.New("w")
+	admitted := 0
+	for _, a := range argTuples() {
+		ok := true
+		for _, x := range a {
+			if !argOkAt("vsxXq", directive{'v', false}, x) {
+				ok = false
+			}
+		}
+		if ok {
+			admitted++
+		}
+		for _, res := range []struct {
+			n   int
+			err error
+		}{{3, nil}, {0, werr}} {
+			calls = nil
+			gw := &recWriter{n: res.n, err: res.err}
+			gn, gerr := fmt.Fprintln(gw, a...)
+			goCalls := calls
+			calls = nil
+			mw := &recWriter{n: res.n, err: res.err}
+			var mn int
+			var merr error
+			stuck := runModel(func() { mn, merr = modelFprintln(mw, a...) })
+			if stuck {
+				if ok {
+					t.Errorf("Fprintln(%s): admitted, but the model is stuck", describe("", a))
+				}
+				continue
+			}
+			if !reflect.DeepEqual(goCalls, calls) {
+				t.Errorf("Fprintln(%s): Go calls %v, the model %v", describe("", a), goCalls, calls)
+			}
+			if len(gw.writes) != 1 || len(mw.writes) != 1 {
+				t.Errorf("Fprintln(%s): Go writes %d times, the model %d", describe("", a),
+					len(gw.writes), len(mw.writes))
+				continue
+			}
+			if !matches(string(mw.writes[0]), string(gw.writes[0])) {
+				t.Errorf("Fprintln(%s) writes %q, the model %q", describe("", a), gw.writes[0],
+					mw.writes[0])
+			}
+			if gn != mn || gerr != merr {
+				t.Errorf("Fprintln(%s) = %d, %v; the model's %d, %v", describe("", a), gn, gerr, mn,
+					merr)
+			}
+		}
+	}
+	t.Logf("%d operand lists admitted", admitted)
+}
+
 // errKind: 0 for an *errors.errorString, 1 for a *fmt.wrapError, 2 for a *fmt.wrapErrors, and
 // what it wraps.
 func errKind(err error) (int, []error) {
```

### goose/model/fmt/model_harness_test.go  (tier 0, translator)

```diff
diff --git a/goose/model/fmt/model_harness_test.go b/goose/model/fmt/model_harness_test.go
new file mode 100644
index 000000000..19d6f2518
--- /dev/null
+++ b/goose/model/fmt/model_harness_test.go
@@ -0,0 +1,135 @@
+package fmt_test
+
+// The harness of the differential tests (model_diff_test.go): model_test.go is the model printer of
+// goose/model/overlay/fmt/printmodel.go, rewritten into this package (model_copy_test.go); here are
+// the stand-ins for what it calls of the overlay's other file (print.go) and of internal/gomodel,
+// and the model's errorf, Fprintf, Fprint and printfFormat (the formatting of the trusted Printf),
+// each the body of the overlay's declaration (print.go) with Go's printer, which the tests cannot
+// reach, left out.
+
+import (
+	"errors"
+	"fmt"
+	"io"
+	"reflect"
+	"strings"
+)
+
+type State = fmt.State
+
+// arbitraryMark stands for an arbitrary string in the model's output (chooseString).
+const arbitraryMark = "\x00<arbitrary>\x00"
+
+func chooseString() string { return arbitraryMark }
+
+// arbitraryChoice is what gomodel.ChooseUint64() returns (arbitrary(); the tests run each choice).
+var arbitraryChoice uint64
+
+func arbitrary() uint64 { return arbitraryChoice }
+
+// arbitraryBool is what gomodel.Choose() returns: false, so that writeArbitrary appends one
+// arbitrary string (one arbitraryMark, which stands for any string, so for any number of them).
+func arbitraryBool() bool { return false }
+
+// buffer is fmt's printer buffer (print.go), with the method the model printer calls.
+type buffer []byte
+
+func (b *buffer) writeString(s string) { *b = append(*b, s...) }
+
+// squash merges adjacent arbitraryMarks (the model's arbitrary strings appended one after
+// another, which stand for any string together).
+func squash(s string) string {
+	for strings.Contains(s, arbitraryMark+arbitraryMark) {
+		s = strings.ReplaceAll(s, arbitraryMark+arbitraryMark, arbitraryMark)
+	}
+	return s
+}
+
+type notModelledPanic struct{}
+
+// notModelled stands for gomodel.Stuck() (no behaviour): the tests see a panic.
+func notModelled() { panic(notModelledPanic{}) }
+
+// underlyingAs is the overlay's primitive stub, with the same Go body.
+func underlyingAs[T any](x any) (T, bool) {
+	var z T
+	if x == nil {
+		return z, false
+	}
+	v := reflect.ValueOf(x)
+	zt := reflect.TypeOf(z)
+	if v.Kind() != zt.Kind() {
+		return z, false
+	}
+	return v.Convert(zt).Interface().(T), true
+}
+
+type wrapError struct {
+	msg string
+	err error
+}
+
+func (e *wrapError) Error() string { return e.msg }
+func (e *wrapError) Unwrap() error { return e.err }
+
+type wrapErrors struct {
+	msg  string
+	errs []error
+}
+
+func (e *wrapErrors) Error() string   { return e.msg }
+func (e *wrapErrors) Unwrap() []error { return e.errs }
+
+// modelSprintf is a probe of the model printer's doPrintf, as a Sprintf (Sprintf itself is the
+// real fmt's).
+func modelSprintf(format string, a ...any) string {
+	var b buffer
+	doPrintf(&b, format, a, false)
+	return squash(string(b))
+}
+
+// modelErrorf is Go's Errorf over the model's errorf (the printer's buffer a fresh one).
+func modelErrorf(format string, a ...any) error {
+	if len(a) == 0 && strings.IndexByte(format, '%') == -1 {
+		return errors.New(format)
+	}
+	var b buffer
+	wrapped, unknown := doPrintf(&b, format, a, true)
+	return errorfResult(squash(string(b)), wrapped, unknown, a)
+}
+
+// modelFprintf is the model's Fprintf: Write gets the bytes doPrintf appends to a fresh buffer.
+func modelFprintf(w io.Writer, format string, a ...any) (int, error) {
+	var b buffer
+	doPrintf(&b, format, a, false)
+	return w.Write([]byte(squash(string(b))))
+}
+
+// modelFprint is Go's Fprint over the model's pp.doPrint.
+func modelFprint(w io.Writer, a ...any) (int, error) {
+	var b buffer
+	for _, x := range a {
+		writeArbitrary(&b)
+		visitArg(x, 'v', false, false)
+	}
+	writeArbitrary(&b)
+	return w.Write([]byte(squash(string(b))))
+}
+
+// modelFprintln is Go's Fprintln over the model's pp.doPrintln.
+func modelFprintln(w io.Writer, a ...any) (int, error) {
+	var b buffer
+	for _, x := range a {
+		writeArbitrary(&b)
+		visitArg(x, 'v', false, false)
+	}
+	writeArbitrary(&b)
+	return w.Write([]byte(squash(string(b))))
+}
+
+// modelPrintfFormat is printfFormat, the formatting of the trusted Printf (the tests compare the
+// calls; the write to os.Stdout is not modelled).
+func modelPrintfFormat(format string, a ...any) {
+	var b buffer
+	doPrintf(&b, format, a, false)
+}
```

### goose/model/fmt/model_test.go  (tier 0, translator)

```diff
diff --git a/goose/model/fmt/model_test.go b/goose/model/fmt/model_test.go
index 5c2408bad..bc45ccf83 100644
--- a/goose/model/fmt/model_test.go
+++ b/goose/model/fmt/model_test.go
@@ -1,82 +1,29 @@
-package fmt_test
+// Code generated from goose/model/overlay/fmt/printmodel.go by model_copy_test.go; DO NOT EDIT.
+
+// The model printer of fmt (Perennial/Code/fmt.toml, [model]): additions that the models of
+// errorf, Fprintf, printfFormat (Printf's) and pp.doPrint (print.go of this directory) call in place of Go's
+// printer for the formatting the real print path is stuck on. Translated like the rest of fmt;
+// they carry no claim of their own: the claims are the MODEL: comments of the replaced
+// declarations, which call them. goose/model/fmt/model_test.go is this file rewritten for the
+// differential tests (goose/model/fmt/model_copy_test.go checks the rewrite).
 
-// The model of fmt.Sprintf, fmt.Printf, fmt.Fprintf, fmt.Fprint and fmt.Errorf (Perennial/TrustedCode/fmt.lean), as the Go
-// its docstrings quote, for the differential tests of model_diff_test.go. Only tests: nothing here
-// is translated. arbitrary, arbitraryString, underlyingAs and notModelled stand for the model's
-// primitives (ArbitraryInt, an arbitrary string, TypeAssertUnderlying2, the stuck points).
+package fmt_test
 
 import (
 	"errors"
-	"fmt"
-	"io"
-	"reflect"
 )
 
-type State = fmt.State
-
-// arbitraryMark stands for an arbitrary string in the model's output.
-const arbitraryMark = "\x00<arbitrary>\x00"
-
-func arbitraryString() string { return arbitraryMark }
-
-// arbitraryChoice is what arbitrary() returns (the tests run each choice).
-var arbitraryChoice uint64
-
-func arbitrary() uint64 { return arbitraryChoice }
-
-type notModelledPanic struct{}
-
-func notModelled() { panic(notModelledPanic{}) }
-
-// printerBuf(s) stands for the printer's buffer Fprintf hands Write (the model's primitive
-// printerBuf): the bytes of s in a slice of arbitrary capacity whose spare capacity holds arbitrary
-// bytes (gc's pooled buffer holds earlier output there), or, for an empty s, possibly nil (gc's
-// fresh printer's buffer, or one after a buffer above 64 KiB was dropped): fprintf_alias_test.go.
-func printerBuf(s string) []byte { return []byte(s) }
-
-// retire(b) stands for the model's primitive retire: every cell of b up to its capacity is left
-// unusable (a write begun and never finished), as gc reuses the buffer for later prints.
-func retire(b []byte) {}
-
-// underlyingAs[T](x): reflect.ValueOf(x) read at T's kind, if x's dynamic type has T's underlying
-// type (TypeAssertUnderlying2 T).
-func underlyingAs[T any](x any) (T, bool) {
-	var z T
-	if x == nil {
-		return z, false
-	}
-	v := reflect.ValueOf(x)
-	zt := reflect.TypeOf(z)
-	if v.Kind() != zt.Kind() {
-		return z, false
-	}
-	return v.Convert(zt).Interface().(T), true
-}
-
-// kindIs[T](x): whether x's dynamic type has T's underlying type (the second result of
-// TypeAssertUnderlying2 T).
+// kindIs[T](x): whether x's dynamic type has T's underlying type. A primitive stub (fmt.toml,
+// trusted), as underlyingAs is: its GooseLang model is the second result of TypeAssertUnderlying2 T
+// (Perennial/TrustedCode/fmt.lean), and this body, for gc builds, is underlyingAs's second result.
+// (It is not translated from this body: a translation binds underlyingAs's first result, the value
+// x holds, which the logic cannot step past for an arbitrary argument, as nothing says that value
+// is not a panic value; isIntKind and isStrKind ask kindIs of any argument.)
 func kindIs[T any](x any) bool {
 	_, ok := underlyingAs[T](x)
 	return ok
 }
 
-type wrapError struct {
-	msg string
-	err error
-}
-
-func (e *wrapError) Error() string { return e.msg }
-func (e *wrapError) Unwrap() error { return e.err }
-
-type wrapErrors struct {
-	msg  string
-	errs []error
-}
-
-func (e *wrapErrors) Error() string   { return e.msg }
-func (e *wrapErrors) Unwrap() []error { return e.errs }
-
-
 func intVerb(format string, i int) (int, int, bool) {
 	if i+1 < len(format) && (format[i+1] == 'd' || format[i+1] == 'v') {
 		return 0, i + 2, true
@@ -216,7 +163,7 @@ func formatHex(neg bool, mag uint64) string {
 	return digits
 }
 
-func modelStrArg(x any) (string, bool) {
+func strArg(x any) (string, bool) {
 	if _, ok := x.(interface{ Format(State, rune) }); ok {
 		return "", false
 	}
@@ -231,11 +178,11 @@ func modelStrArg(x any) (string, bool) {
 
 func formatArg(format string, i int, x any) (string, int, bool) {
 	if i+1 < len(format) && format[i+1] == 's' {
-		s, ok := modelStrArg(x)
+		s, ok := strArg(x)
 		return s, i + 2, ok
 	}
 	if i+1 < len(format) && format[i+1] == 'v' {
-		if s, ok := modelStrArg(x); ok {
+		if s, ok := strArg(x); ok {
 			return s, i + 2, true
 		}
 	}
@@ -395,10 +342,6 @@ func formatSlice(format string, i int, x any) (string, int, bool) {
 	return "", 0, false
 }
 
-// The new parts of the model of fmt (Perennial/TrustedCode/fmt.lean). In the scratch package these
-// sit next to the old helpers (oldmodel.go), with stubs for arbitrary, arbitraryString,
-// underlyingAs and notModelled.
-
 // isBasic: whether x's dynamic type is one of the predeclared types that printArg formats by its
 // type switch, without handleMethods (bool, the integer types, uintptr, float32, float64, string;
 // not complex64, complex128 or []byte, which the model does not follow, nor reflect.Value, which
@@ -607,9 +550,13 @@ func visitArg(x any, verb byte, sharpV bool, wrapErrs bool) {
 
 // visitRest goes through the directives of format from index i, the arguments from argNum,
 // calling what Go calls of each argument (visitArg), and then of each argument left over (Go's
-// %!(EXTRA ...), under %v). It returns the indices of the arguments of the %w directives, and
-// whether it gave up at a directive the model does not follow, every argument being inert.
-func visitRest(format string, i int, a []any, argNum int, wrapErrs bool) ([]int, bool) {
+// %!(EXTRA ...), under %v). Before each argument it appends arbitrary strings to b
+// (writeArbitrary): what Go's printer has appended to its buffer by then, which a method of the
+// argument can read through a slice of the buffer that a writer kept (Fprintf hands the buffer to
+// w.Write, and the pool hands the printer out again). It returns the indices of the arguments of
+// the %w directives, and whether it gave up at a directive the model does not follow, every
+// argument being inert.
+func visitRest(b *buffer, format string, i int, a []any, argNum int, wrapErrs bool) ([]int, bool) {
 	var wrapped []int
 	for i < len(format) {
 		if format[i] != '%' {
@@ -633,21 +580,36 @@ func visitRest(format string, i int, a []any, argNum int, wrapErrs bool) ([]int,
 		if verb == 'w' {
 			wrapped = append(wrapped, argNum)
 		}
+		writeArbitrary(b)
 		visitArg(a[argNum], byte(verb), sharpV, wrapErrs)
 		argNum++
 	}
 	for argNum < len(a) {
+		writeArbitrary(b)
 		visitArg(a[argNum], 'v', false, wrapErrs)
 		argNum++
 	}
 	return wrapped, false
 }
 
-// doPrintf: the formatted string, the indices of the arguments of the %w directives, and whether
-// those are unknown (visitRest gave up). It formats as the previous model of Sprintf did, up to
-// the first directive it does not format or whose argument is not inert; from there the output is
-// arbitrary, and visitRest makes the calls Go makes.
-func doPrintf(format string, a []any, wrapErrs bool) (string, []int, bool) {
+// writeArbitrary appends one or more arbitrary strings to b (chooseString), each with one
+// writeString: Go's printer appends to its buffer piece by piece, and as GooseLang's append chooses
+// a new capacity freely when it reallocates, these appends can leave b as Go's leaves its buffer,
+// in content, backing array and capacity.
+func writeArbitrary(b *buffer) {
+	b.writeString(chooseString())
+	for arbitraryBool() {
+		b.writeString(chooseString())
+	}
+}
+
+// doPrintf appends the formatted string to b and returns the indices of the arguments of the %w
+// directives, and whether those are unknown (visitRest gave up). It formats as the trusted model of
+// Sprintf did before stage 1 of perennial#671, up to the first directive it does not format or
+// whose argument is not inert, and appends that prefix to b, which Go's printer has appended by
+// then, before any method call; from there visitRest makes the calls Go makes, with arbitrary
+// strings appended before each, and arbitrary strings end the output.
+func doPrintf(b *buffer, format string, a []any, wrapErrs bool) ([]int, bool) {
 	var out string
 	var argNum int
 	var i int
@@ -680,52 +642,28 @@ func doPrintf(format string, a []any, wrapErrs bool) (string, []int, bool) {
 				continue
 			}
 		}
-		wrapped, unknown := visitRest(format, i, a, argNum, wrapErrs)
-		return out + arbitraryString(), wrapped, unknown
+		b.writeString(out)
+		wrapped, unknown := visitRest(b, format, i, a, argNum, wrapErrs)
+		writeArbitrary(b)
+		return wrapped, unknown
 	}
+	b.writeString(out)
 	if argNum < len(a) {
-		wrapped, unknown := visitRest(format, i, a, argNum, wrapErrs)
-		return out + arbitraryString(), wrapped, unknown
-	}
-	return out, nil, false
-}
-
-// modelSprintf is a test probe of the model's doPrintf, as a Sprintf: the Lean model has no
-// Sprintf (Sprintf is the real fmt's, translated).
-func modelSprintf(format string, a ...any) string {
-	s, _, _ := doPrintf(format, a, false)
-	return s
-}
-
-func modelPrintf(format string, a ...any) (int, error) {
-	doPrintf(format, a, false)
-	n := int(arbitrary())
-	if arbitrary() == 0 {
-		return n, nil
-	}
-	return n, errors.New(arbitraryString())
-}
-
-func modelFprintf(w io.Writer, format string, a ...any) (int, error) {
-	s, _, _ := doPrintf(format, a, false)
-	b := printerBuf(s)
-	n, err := w.Write(b)
-	retire(b)
-	return n, err
-}
-
-func modelFprint(w io.Writer, a ...any) (int, error) {
-	for _, x := range a {
-		visitArg(x, 'v', false, false)
+		wrapped, unknown := visitRest(b, format, i, a, argNum, wrapErrs)
+		writeArbitrary(b)
+		return wrapped, unknown
 	}
-	b := printerBuf(arbitraryString())
-	n, err := w.Write(b)
-	retire(b)
-	return n, err
+	return nil, false
 }
 
-func modelErrorf(format string, a ...any) error {
-	s, wrapped, unknown := doPrintf(format, a, true)
+// errorfResult: the error errorf returns of the message s, the indices wrapped of the arguments
+// of its %w directives, and whether those are unknown (doPrintf's results): errors.New(s) when no
+// %w directive had an argument, a *wrapError holding the argument as an error (nil if it is not
+// one) when one had, a *wrapErrors holding those of the arguments that are errors when several
+// had (Go sorts and deduplicates them only after an argument index, which the model does not
+// follow: parseDirective refuses '['). Where doPrintf gave up on a directive it does not follow,
+// every argument being inert (none is an error), the error is any of the three, holding no error.
+func errorfResult(s string, wrapped []int, unknown bool, a []any) error {
 	if unknown {
 		n := arbitrary()
 		if n == 0 {
```

### goose/model/fmt/sprintf_test.go  (tier 0, translator)

```diff
diff --git a/goose/model/fmt/sprintf_test.go b/goose/model/fmt/sprintf_test.go
index a39653e33..d1d947eaf 100644
--- a/goose/model/fmt/sprintf_test.go
+++ b/goose/model/fmt/sprintf_test.go
@@ -1,12 +1,11 @@
-// Package fmt_test checks, against Go's fmt, the behaviour of fmt.Sprintf that the trusted model's
-// doPrintf in Perennial/TrustedCode/fmt.lean (formatArg) relies on; Printf, Fprintf and Errorf
-// format with it (Sprintf itself is the real fmt's, translated). Only tests: nothing here is
-// translated.
+// Package fmt_test checks, against Go's fmt, the behaviour of fmt.Sprintf that the model printer's
+// doPrintf (goose/model/overlay/fmt/printmodel.go: formatArg, strArg) relies on; the models of
+// errorf, Fprintf and Printf format with it (Sprintf itself is the real fmt's, translated). Only
+// tests: nothing here is translated.
 package fmt_test
 
 import (
 	"fmt"
-	"reflect"
 	"testing"
 )
 
@@ -43,28 +42,6 @@ type ptrStringName string
 
 func (s *ptrStringName) String() string { return "P" }
 
-// The model's strArg (Perennial/TrustedCode/fmt.lean), with underlyingAs[string] as
-// reflect.ValueOf(x).String() at kind String (TypeAssertUnderlying2 go.string).
-func strArg(x any) (string, bool) {
-	if _, ok := x.(interface{ Format(fmt.State, rune) }); ok {
-		return "", false
-	}
-	if _, ok := x.(interface{ String() string }); ok {
-		return "", false
-	}
-	if _, ok := x.(error); ok {
-		return "", false
-	}
-	if x == nil {
-		return "", false
-	}
-	v := reflect.ValueOf(x)
-	if v.Kind() != reflect.String {
-		return "", false
-	}
-	return v.String(), true
-}
-
 // %v of a string is the string itself, byte for byte, as %s gives it; alone, inside other text,
 // and next to other directives. (The model formats %v of an interface holding a `string` so.)
 func TestSprintfVString(t *testing.T) {
```

### goose/model/fmt/testdata/alias/alias_goose_test.go  (tier 0, translator)

```diff
diff --git a/goose/model/fmt/testdata/alias/alias_goose_test.go b/goose/model/fmt/testdata/alias/alias_goose_test.go
new file mode 100644
index 000000000..7e1cb2e55
--- /dev/null
+++ b/goose/model/fmt/testdata/alias/alias_goose_test.go
@@ -0,0 +1,7 @@
+//go:build goose
+
+package fmt_test
+
+import "internal/gomodel"
+
+func init() { drive = gomodel.Drive }
```

### goose/model/fmt/testdata/alias/alias_test.go  (tier 0, translator)

```diff
diff --git a/goose/model/fmt/testdata/alias/alias_test.go b/goose/model/fmt/testdata/alias/alias_test.go
new file mode 100644
index 000000000..f0f882589
--- /dev/null
+++ b/goose/model/fmt/testdata/alias/alias_test.go
@@ -0,0 +1,108 @@
+// TestModelAlias: the printer's buffer, which Fprintf and Fprint hand to w.Write, is observable
+// outside fmt. A writer that keeps the slice aliases the buffer of the printer that fmt's pool
+// (ppFree) hands out again, so a later Errorf's message, or what a String method reads or writes
+// through the slice while Fprintf or Fprint prints, depends on what the printer appended to its
+// buffer and when (the adversarial review of S3's fmt models, gmr-adv-fmt/demo).
+//
+// The test is a file of package fmt_test that etc/model-tests.sh adds to the standard library's
+// fmt with go test -overlay, twice: on the real fmt, where it checks that Go gives the results
+// below (the scenario reuses the pooled printer, as gc's sync.Pool does with the garbage collector
+// off and one goroutine); and on fmt with its Go models (with -tags goose, the internal/gomodel of
+// gomodel_driven.go), where it checks that the model gives the same results, for the choices of
+// Choose and ChooseUint64 that each case drives: Go's results are among the model's.
+package fmt_test
+
+import (
+	"fmt"
+	"runtime/debug"
+	"testing"
+)
+
+// drive makes the model's next choices those of s (alias_goose_test.go); on the real fmt, which
+// chooses nothing, it does nothing.
+var drive = func(s []uint64) {}
+
+var saved []byte
+
+// keep is a writer that keeps the slice Write receives: the printer's buffer.
+type keep struct{}
+
+func (keep) Write(b []byte) (int, error) { saved = b; return len(b), nil }
+
+// rec is a writer that records a copy of what Write receives.
+type rec struct{ got string }
+
+func (r *rec) Write(b []byte) (int, error) { r.got = string(b); return len(b), nil }
+
+var seen string
+
+// peek reads the kept slice while fmt prints.
+type peek struct{}
+
+func (peek) String() string { seen = string(saved[:4]); return "" }
+
+// poke writes into the kept slice while fmt prints.
+type poke struct{}
+
+func (poke) String() string { saved[0] = 'Z'; return "" }
+
+// chooseStringScript is the choices that make the model's chooseString return s.
+func chooseStringScript(s string) []uint64 {
+	var c []uint64
+	for i := 0; i < len(s); i++ {
+		c = append(c, 1, uint64(s[i]))
+	}
+	return append(c, 0)
+}
+
+func TestModelAlias(t *testing.T) {
+	defer debug.SetGCPercent(debug.SetGCPercent(-1))
+	cases := []struct {
+		name   string
+		script []uint64
+		run    func() string
+		want   string
+	}{
+		{"Errorf's message in the kept buffer", nil, func() string {
+			fmt.Fprintf(keep{}, "hello world")
+			_ = fmt.Errorf("abc %d", 5)
+			return string(saved)
+		}, "abc 5 world"},
+		{"Fprintf: a String method reads the buffer", nil, func() string {
+			fmt.Fprintf(keep{}, "hello world")
+			fmt.Fprintf(keep{}, "XYZW%v", peek{})
+			return seen
+		}, "XYZW"},
+		// The model: "XYZW" appended (writeArbitrary: chooseString, then Choose false) before the
+		// first operand, nothing before the second.
+		{"Fprint: a String method reads the buffer", append(chooseStringScript("XYZW"), 0), func() string {
+			fmt.Fprintf(keep{}, "hello world")
+			fmt.Fprint(keep{}, "XYZW", peek{})
+			return seen
+		}, "XYZW"},
+		{"Fprintf: a String method writes the buffer", nil, func() string {
+			fmt.Fprintf(keep{}, "hello world")
+			var r rec
+			fmt.Fprintf(&r, "ab%v", poke{})
+			return r.got
+		}, "Zb"},
+		{"Errorf: a String method writes the buffer", nil, func() string {
+			fmt.Fprintf(keep{}, "hello world")
+			return fmt.Errorf("ab%v", poke{}).Error()
+		}, "Zb"},
+	}
+	for _, c := range cases {
+		// The pool may (rarely) hand out another printer, if the goroutine moved to another P:
+		// try a few times.
+		var got string
+		for try := 0; try < 5; try++ {
+			drive(c.script)
+			if got = c.run(); got == c.want {
+				break
+			}
+		}
+		if got != c.want {
+			t.Errorf("%s: %q, want %q", c.name, got, c.want)
+		}
+	}
+}
```

### goose/model/fmt/testdata/alias/gomodel_driven.go  (tier 0, translator)

```diff
diff --git a/goose/model/fmt/testdata/alias/gomodel_driven.go b/goose/model/fmt/testdata/alias/gomodel_driven.go
new file mode 100644
index 000000000..f058b15be
--- /dev/null
+++ b/goose/model/fmt/testdata/alias/gomodel_driven.go
@@ -0,0 +1,31 @@
+// internal/gomodel with its choices driven by a test (TestModelAlias, alias_test.go): the overlay's
+// gomodel.go (goose/model/overlay/internal/gomodel), but Choose and ChooseUint64 return, in order,
+// the values a test gives with Drive (Choose: whether the value is not 0), then 0 once those run
+// out. etc/model-tests.sh puts it in place of gomodel.go for the fmt alias test only.
+package gomodel
+
+var script []uint64
+
+// Drive makes the next calls of Choose and ChooseUint64 return the values of s, in order.
+func Drive(s []uint64) { script = append([]uint64(nil), s...) }
+
+func next() uint64 {
+	if len(script) == 0 {
+		return 0
+	}
+	v := script[0]
+	script = script[1:]
+	return v
+}
+
+// Choose is an arbitrary boolean (GooseLang: any). Here, the next driven value is not 0.
+func Choose() bool { return next() != 0 }
+
+// ChooseUint64 is an arbitrary uint64 (GooseLang: any). Here, the next driven value.
+func ChooseUint64() uint64 { return next() }
+
+// Stuck has no behaviour (GooseLang: stuck). Here, it blocks forever.
+func Stuck() { select {} }
+
+// StartRead (GooseLang: makes *p read-only). Here, it does nothing.
+func StartRead[T any](p *T) {}
```

### goose/model/overlay/fmt/print.go  (tier 0, go-model-overlay)

```diff
diff --git a/goose/model/overlay/fmt/print.go b/goose/model/overlay/fmt/print.go
new file mode 100644
index 000000000..59034e992
--- /dev/null
+++ b/goose/model/overlay/fmt/print.go
@@ -0,0 +1,152 @@
+// The Go models of fmt (Perennial/Code/fmt.toml, [model]): errorf, Fprintf, pp.doPrint and
+// pp.doPrintln, spliced into errors.go and print.go in place of the real declarations, printfFormat
+// (the formatting of Printf, which is trusted: Perennial/TrustedCode/fmt.lean), and the additions
+// they need besides the model printer (printmodel.go). Sprintf, Errorf, Fprint, Fprintln and the
+// real printer stay Go's own, translated.
+//
+// Why models at all: the real print path (pp.doPrintf, pp.printArg) is translated and proved only
+// on stage 1's subset (fmt.Fits, perennial#671). Elsewhere it is stuck: on floats and complex
+// numbers (strconv.AppendFloat and pp.fmtComplex are not translated), on %q of an integer
+// (strconv.AppendQuoteRune), on %T, %p, a bad verb and %!(EXTRA ...) (reflect.TypeOf), and on
+// named integer and string types, a []string, and a value of integer kind with String or Error
+// under a non-method verb (pp.printValue, which reflects). The specs of Errorf, Printf, Fprintf
+// and Fprint admit those calls (fmt.argsOk, fmt.printArgOk), so these four print with the model
+// printer instead (Printf through printfFormat): doPrintf formats exactly the common directives of inert arguments and of a
+// []byte or []string, appending them to the printer's buffer p.buf as Go does, and from the first
+// other directive on appends arbitrary strings, before each call of an argument's Error() or
+// String() (where Go's handleMethods calls it) and at the end. The buffer is observable outside
+// fmt: Fprintf and Fprint hand p.buf to w.Write, and a writer that keeps the slice aliases the
+// buffer of a printer the pool (ppFree) hands out again, to a later errorf, Fprintf or Fprint, or
+// to a method that the same call calls; so the model appends to p.buf what Go has appended by each
+// method call (an arbitrary string covers it), and errorf reads its message back from p.buf. it is stuck (notModelled)
+// where it does not follow Go: a Format or GoString method Go would call, a reflect.Value,
+// reflection into a struct, pointer, map or other slice, an argument index or a '*' width with an
+// argument that is not inert, a method that panics (Go's catchPanic recovers it). Its output is
+// Go's, the arbitrary strings standing for any suffix, and it calls the methods Go calls in Go's
+// order: model ⊇ Go, checked by goose/model/fmt/model_diff_test.go (TestModelSprintf,
+// TestModelBytesExact, TestModelStringsExact, TestModelErrorf, TestModelFprintf, TestModelFprint,
+// TestModelFprintln, TestModelPrintf) and sprintf_test.go, and, for the buffer, by TestModelAlias
+// (testdata/alias, run by etc/model-tests.sh under the overlay).
+
+package fmt
+
+import (
+	"internal/gomodel"
+	"internal/stringslite"
+	"io"
+	"reflect"
+)
+
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
+func errorf(format string, a ...any) error {
+	if len(a) == 0 && stringslite.IndexByte(format, '%') == -1 {
+		return nil
+	}
+	p := newPrinter()
+	wrapped, unknown := doPrintf(&p.buf, format, a, true)
+	s := string(p.buf)
+	err := errorfResult(s, wrapped, unknown, a)
+	p.free()
+	return err
+}
+
+// MODEL: Fprintf is Go's, but for one line: Go's p.doPrintf(format, a) is the model printer's
+// doPrintf(&p.buf, format, a, false), which appends to p.buf what Go appends up to its first
+// method call or directive the model does not format, and arbitrary strings from there, before
+// each method call and at the end (see the file comment for what the model printer covers and
+// where it is stuck; TestModelFprintf checks the bytes Write receives and the methods called;
+// TestModelAlias a method reading p.buf through a slice an earlier Write kept). The printer, its
+// pool (ppFree), the one w.Write(p.buf) and p.free() are Go's own.
+func Fprintf(w io.Writer, format string, a ...any) (n int, err error) {
+	p := newPrinter()
+	doPrintf(&p.buf, format, a, false)
+	n, err = w.Write(p.buf)
+	p.free()
+	return
+}
+
+// printfFormat is Printf's formatting, a helper of its trusted model (Perennial/TrustedCode/fmt.lean,
+// fmt.toml's trusted), not a function of package fmt: Go's Printf is Fprintf(os.Stdout, format,
+// a...), whose printer, model doPrintf (as in Fprintf above) and p.free() this is, without the
+// write to os.Stdout; the trusted Printf returns an arbitrary count and either nil or an arbitrary
+// error for it (the model of os has no Stdout, and translating the write would need a semantics
+// primitive for an arbitrary interface value, Go's error of it).
+func printfFormat(format string, a []any) {
+	p := newPrinter()
+	doPrintf(&p.buf, format, a, false)
+	p.free()
+}
+
+// MODEL: pp.doPrint prints the operands under %v, a space between two that are not strings. Go
+// tells a string by reflect.TypeOf(arg).Kind() == reflect.String (reflection, which is stuck) and
+// prints each with p.printArg, which is stuck on the operands of the file comment; Fprint's spec
+// admits them (fmt.printArgOk). The model calls of each operand what Go's printArg calls under %v
+// (visitArg: its Error() or String(), stuck where the model printer is), after appending arbitrary
+// strings to p.buf (writeArbitrary), which stand for what Go has appended by then (a method may
+// read p.buf through a slice a writer kept), and appends arbitrary strings at the end, for the
+// rest of Go's output (TestModelFprint checks the calls, TestModelAlias the buffer). Fprint and
+// Sprint, Go's own, print with it.
+func (p *pp) doPrint(a []any) {
+	for _, x := range a {
+		writeArbitrary(&p.buf)
+		visitArg(x, 'v', false, false)
+	}
+	writeArbitrary(&p.buf)
+}
+
+// MODEL: pp.doPrintln is doPrint's model (see there): Go's doPrintln, for each operand, appends a
+// space if it is not the first and prints it with p.printArg(arg, 'v'), then appends '\n'; the
+// model calls of each operand what printArg calls under %v (visitArg), after arbitrary strings
+// (writeArbitrary), which cover Go's space and what printArg appended before, and ends with
+// arbitrary strings, which cover the rest and the newline (TestModelFprintln checks the calls).
+// Fprintln and Sprintln, Go's own, print with it.
+func (p *pp) doPrintln(a []any) {
+	for _, x := range a {
+		writeArbitrary(&p.buf)
+		visitArg(x, 'v', false, false)
+	}
+	writeArbitrary(&p.buf)
+}
+
+// chooseString is an arbitrary string, the model printer's output from where it stops following
+// Go: it can return every string (and may also not terminate, which partial correctness allows).
+func chooseString() string {
+	var s string
+	for gomodel.ChooseUint64() != 0 {
+		s += string([]byte{byte(gomodel.ChooseUint64())})
+	}
+	return s
+}
+
+// notModelled is the model printer's stuck point, where it does not follow Go: gomodel.Stuck.
+func notModelled() {
+	gomodel.Stuck()
+}
+
+// underlyingAs[T](x) is x's value converted to T and true, if x's dynamic type has T's underlying
+// type, and the zero T and false otherwise (also for a nil x): reflect.ValueOf(x).Kind() is T's
+// kind, which plain Go cannot test without reflection. A primitive stub (fmt.toml, trusted): its
+// GooseLang model is TypeAssertUnderlying2 T (Perennial/TrustedCode/fmt.lean), and this body, for
+// gc builds, is the reflection, for the integer types and string that the model printer asks.
+func underlyingAs[T any](x any) (T, bool) {
+	var z T
+	if x == nil {
+		return z, false
+	}
+	v := reflect.ValueOf(x)
+	zt := reflect.TypeOf(z)
+	if v.Kind() != zt.Kind() {
+		return z, false
+	}
+	return v.Convert(zt).Interface().(T), true
+}
```

### goose/model/overlay/fmt/printmodel.go  (tier 0, go-model-overlay)

```diff
diff --git a/goose/model/overlay/fmt/printmodel.go b/goose/model/overlay/fmt/printmodel.go
new file mode 100644
index 000000000..010b0cd6c
--- /dev/null
+++ b/goose/model/overlay/fmt/printmodel.go
@@ -0,0 +1,691 @@
+// The model printer of fmt (Perennial/Code/fmt.toml, [model]): additions that the models of
+// errorf, Fprintf, printfFormat (Printf's) and pp.doPrint (print.go of this directory) call in place of Go's
+// printer for the formatting the real print path is stuck on. Translated like the rest of fmt;
+// they carry no claim of their own: the claims are the MODEL: comments of the replaced
+// declarations, which call them. goose/model/fmt/model_test.go is this file rewritten for the
+// differential tests (goose/model/fmt/model_copy_test.go checks the rewrite).
+
+package fmt
+
+import (
+	"errors"
+	"internal/gomodel"
+)
+
+// kindIs[T](x): whether x's dynamic type has T's underlying type. A primitive stub (fmt.toml,
+// trusted), as underlyingAs is: its GooseLang model is the second result of TypeAssertUnderlying2 T
+// (Perennial/TrustedCode/fmt.lean), and this body, for gc builds, is underlyingAs's second result.
+// (It is not translated from this body: a translation binds underlyingAs's first result, the value
+// x holds, which the logic cannot step past for an arbitrary argument, as nothing says that value
+// is not a panic value; isIntKind and isStrKind ask kindIs of any argument.)
+func kindIs[T any](x any) bool {
+	_, ok := underlyingAs[T](x)
+	return ok
+}
+
+func intVerb(format string, i int) (int, int, bool) {
+	if i+1 < len(format) && (format[i+1] == 'd' || format[i+1] == 'v') {
+		return 0, i + 2, true
+	}
+	if i+1 < len(format) && format[i+1] == '0' {
+		j := i + 2
+		var width int
+		for j < len(format) && '0' <= format[j] && format[j] <= '9' && width <= 1000000 {
+			width = width*10 + int(format[j]-'0')
+			j++
+		}
+		if j > i+2 && j < len(format) && format[j] == 'd' && width <= 1000000 {
+			return width, j + 1, true
+		}
+	}
+	return 0, 0, false
+}
+
+func intArg(x any) (bool, uint64, bool) {
+	var n int64
+	if v, ok := x.(int); ok {
+		n = int64(v)
+	} else if v, ok := x.(int64); ok {
+		n = v
+	} else if v, ok := x.(int32); ok {
+		n = int64(v)
+	} else if v, ok := x.(int16); ok {
+		n = int64(v)
+	} else if v, ok := x.(int8); ok {
+		n = int64(v)
+	} else if v, ok := x.(uint); ok {
+		return false, uint64(v), true
+	} else if v, ok := x.(uint64); ok {
+		return false, v, true
+	} else if v, ok := x.(uint32); ok {
+		return false, uint64(v), true
+	} else if v, ok := x.(uint16); ok {
+		return false, uint64(v), true
+	} else if v, ok := x.(uint8); ok {
+		return false, uint64(v), true
+	} else {
+		return false, 0, false
+	}
+	if n < 0 {
+		return true, uint64(-n), true
+	}
+	return false, uint64(n), true
+}
+
+func namedIntArg(x any) (bool, uint64, bool) {
+	if _, ok := x.(interface{ Format(State, rune) }); ok {
+		return false, 0, false
+	}
+	if _, ok := x.(interface{ String() string }); ok {
+		return false, 0, false
+	}
+	if _, ok := x.(error); ok {
+		return false, 0, false
+	}
+	var n int64
+	if v, ok := underlyingAs[int](x); ok {
+		n = int64(v)
+	} else if v, ok := underlyingAs[int64](x); ok {
+		n = v
+	} else if v, ok := underlyingAs[int32](x); ok {
+		n = int64(v)
+	} else if v, ok := underlyingAs[int16](x); ok {
+		n = int64(v)
+	} else if v, ok := underlyingAs[int8](x); ok {
+		n = int64(v)
+	} else if v, ok := underlyingAs[uint](x); ok {
+		return false, uint64(v), true
+	} else if v, ok := underlyingAs[uint64](x); ok {
+		return false, v, true
+	} else if v, ok := underlyingAs[uint32](x); ok {
+		return false, uint64(v), true
+	} else if v, ok := underlyingAs[uint16](x); ok {
+		return false, uint64(v), true
+	} else if v, ok := underlyingAs[uint8](x); ok {
+		return false, uint64(v), true
+	} else {
+		return false, 0, false
+	}
+	if n < 0 {
+		return true, uint64(-n), true
+	}
+	return false, uint64(n), true
+}
+
+func anyIntArg(x any) (bool, uint64, bool) {
+	neg, mag, ok := intArg(x)
+	if ok {
+		return neg, mag, true
+	}
+	return namedIntArg(x)
+}
+
+func formatInt(neg bool, mag uint64, width int) string {
+	var digits string
+	for {
+		digits = string([]byte{byte(mag%10) + '0'}) + digits
+		mag = mag / 10
+		if mag == 0 {
+			break
+		}
+	}
+	if neg {
+		width--
+	}
+	for len(digits) < width {
+		digits = "0" + digits
+	}
+	if neg {
+		return "-" + digits
+	}
+	return digits
+}
+
+func formatHex(neg bool, mag uint64) string {
+	var digits string
+	for {
+		d := byte(mag % 16)
+		if d < 10 {
+			d = '0' + d
+		} else {
+			d = 'a' + (d - 10)
+		}
+		digits = string([]byte{d}) + digits
+		mag = mag / 16
+		if mag == 0 {
+			break
+		}
+	}
+	if neg {
+		return "-" + digits
+	}
+	return digits
+}
+
+func strArg(x any) (string, bool) {
+	if _, ok := x.(interface{ Format(State, rune) }); ok {
+		return "", false
+	}
+	if _, ok := x.(interface{ String() string }); ok {
+		return "", false
+	}
+	if _, ok := x.(error); ok {
+		return "", false
+	}
+	return underlyingAs[string](x)
+}
+
+func formatArg(format string, i int, x any) (string, int, bool) {
+	if i+1 < len(format) && format[i+1] == 's' {
+		s, ok := strArg(x)
+		return s, i + 2, ok
+	}
+	if i+1 < len(format) && format[i+1] == 'v' {
+		if s, ok := strArg(x); ok {
+			return s, i + 2, true
+		}
+	}
+	if i+1 < len(format) && format[i+1] == 'x' {
+		neg, mag, ok := anyIntArg(x)
+		if !ok {
+			return "", 0, false
+		}
+		return formatHex(neg, mag), i + 2, true
+	}
+	width, next, ok := intVerb(format, i)
+	if !ok {
+		return "", 0, false
+	}
+	neg, mag, ok2 := anyIntArg(x)
+	if !ok2 {
+		return "", 0, false
+	}
+	return formatInt(neg, mag, width), next, true
+}
+
+// hexNibble: the hexadecimal digit of d (below 16), lowercase or uppercase.
+func hexNibble(d byte, upper bool) byte {
+	if d < 10 {
+		return '0' + d
+	}
+	if upper {
+		return 'A' + (d - 10)
+	}
+	return 'a' + (d - 10)
+}
+
+// quoteByte: the byte c as strconv.Quote writes it inside the quotes, for c below 0x80: \" and
+// \\, the bytes from 0x20 to 0x7E themselves, the escapes \a \b \f \n \r \t \v, and \xNN for the
+// other control bytes and 0x7F. (Of a byte from 0x80 it gives \xNN too; quoteBytes never asks.)
+func quoteByte(c byte) string {
+	if c == '"' || c == '\\' {
+		return string([]byte{'\\', c})
+	}
+	if 0x20 <= c && c <= 0x7e {
+		return string([]byte{c})
+	}
+	if c == '\a' {
+		return `\a`
+	}
+	if c == '\b' {
+		return `\b`
+	}
+	if c == '\f' {
+		return `\f`
+	}
+	if c == '\n' {
+		return `\n`
+	}
+	if c == '\r' {
+		return `\r`
+	}
+	if c == '\t' {
+		return `\t`
+	}
+	if c == '\v' {
+		return `\v`
+	}
+	return string([]byte{'\\', 'x', hexNibble(c/16, false), hexNibble(c%16, false)})
+}
+
+// quoteBytes: strconv.Quote(string(b)), as fmtQ prints %q of b without flags, width or
+// precision, when every byte of b is ASCII (below 0x80): there strconv's escaping depends on no
+// table (IsPrint is true exactly from 0x20 to 0x7E). ok is false when a byte is not ASCII, where
+// strconv decodes UTF-8 and consults its printable-rune tables.
+func quoteBytes(b []byte) (string, bool) {
+	out := "\""
+	for _, c := range b {
+		if c >= 0x80 {
+			return "", false
+		}
+		out += quoteByte(c)
+	}
+	return out + "\"", true
+}
+
+// decBytes: %v and %d of b, as fmtBytes prints them: its bytes in decimal, separated by spaces,
+// in brackets.
+func decBytes(b []byte) string {
+	out := "["
+	for k, c := range b {
+		if k > 0 {
+			out += " "
+		}
+		out += formatInt(false, uint64(c), 0)
+	}
+	return out + "]"
+}
+
+// hexBytes: %x (upper false) and %X of b, as fmtBytes prints them: two hexadecimal digits a byte.
+func hexBytes(b []byte, upper bool) string {
+	var out string
+	for _, c := range b {
+		out += string([]byte{hexNibble(c/16, upper), hexNibble(c%16, upper)})
+	}
+	return out
+}
+
+// joinStrings: %v and %s of ss, as printValue prints a []string: its elements (each by fmtS, the
+// string itself), separated by spaces, in brackets.
+func joinStrings(ss []string) string {
+	out := "["
+	for k, s := range ss {
+		if k > 0 {
+			out += " "
+		}
+		out += s
+	}
+	return out + "]"
+}
+
+// formatSlice: at format[i], a '%': the output of the directive for the argument x, if it is of
+// type []byte or []string, and the index after it. Of a []byte, as Go's fmtBytes prints it, if
+// the directive is %s, %v, %d, %x, %X or %q, without flags, width or precision (%q only of ASCII
+// bytes, quoteBytes). Of a []string, as printValue prints it (no method of a []string or a string
+// to call), if the directive is %s or %v without flags, width or precision (joinStrings). It reads
+// every byte or element of x then, as Go does, and nothing otherwise.
+func formatSlice(format string, i int, x any) (string, int, bool) {
+	if i+1 >= len(format) {
+		return "", 0, false
+	}
+	verb := format[i+1]
+	if verb != 's' && verb != 'v' && verb != 'd' && verb != 'x' && verb != 'X' && verb != 'q' {
+		return "", 0, false
+	}
+	if ss, ok := x.([]string); ok {
+		if verb == 's' || verb == 'v' {
+			return joinStrings(ss), i + 2, true
+		}
+		return "", 0, false
+	}
+	b, ok := x.([]byte)
+	if !ok {
+		return "", 0, false
+	}
+	if verb == 's' {
+		return string(b), i + 2, true
+	}
+	if verb == 'v' || verb == 'd' {
+		return decBytes(b), i + 2, true
+	}
+	if verb == 'x' || verb == 'X' {
+		return hexBytes(b, verb == 'X'), i + 2, true
+	}
+	if verb == 'q' {
+		s, ok := quoteBytes(b)
+		if !ok {
+			return "", 0, false
+		}
+		return s, i + 2, true
+	}
+	return "", 0, false
+}
+
+// isBasic: whether x's dynamic type is one of the predeclared types that printArg formats by its
+// type switch, without handleMethods (bool, the integer types, uintptr, float32, float64, string;
+// not complex64, complex128 or []byte, which the model does not follow, nor reflect.Value, which
+// printArg unwraps: visitArg is stuck on a Stringer with a CanInterface() bool method, as it has).
+func isBasic(x any) bool {
+	switch x.(type) {
+	case bool, int, int8, int16, int32, int64, uint, uint8, uint16, uint32, uint64, uintptr,
+		float32, float64, string:
+		return true
+	}
+	return false
+}
+
+// isIntKind: whether x's dynamic type has an integer kind (one of Go's ten integer types as its
+// underlying type; not uintptr).
+func isIntKind(x any) bool {
+	return kindIs[int](x) || kindIs[int64](x) || kindIs[int32](x) || kindIs[int16](x) ||
+		kindIs[int8](x) || kindIs[uint](x) || kindIs[uint64](x) || kindIs[uint32](x) ||
+		kindIs[uint16](x) || kindIs[uint8](x)
+}
+
+// isStrKind: whether x's dynamic type has kind String.
+func isStrKind(x any) bool {
+	return kindIs[string](x)
+}
+
+// hasFmtMethod: whether x implements one of the interfaces handleMethods consults (Formatter,
+// GoStringer, error, Stringer).
+func hasFmtMethod(x any) bool {
+	if _, ok := x.(interface{ Format(State, rune) }); ok {
+		return true
+	}
+	if _, ok := x.(interface{ GoString() string }); ok {
+		return true
+	}
+	if _, ok := x.(error); ok {
+		return true
+	}
+	if _, ok := x.(interface{ String() string }); ok {
+		return true
+	}
+	return false
+}
+
+// inert: whether Go formats x, under any directive, without calling any of its methods or reading
+// memory: nil, a predeclared basic type, or a type of integer or string kind that implements none
+// of handleMethods' interfaces.
+func inert(x any) bool {
+	if x == nil {
+		return true
+	}
+	if isBasic(x) {
+		return true
+	}
+	if hasFmtMethod(x) {
+		return false
+	}
+	if isStrKind(x) {
+		return true
+	}
+	return isIntKind(x)
+}
+
+// allInert: whether every argument is inert.
+func allInert(a []any) bool {
+	for _, x := range a {
+		if !inert(x) {
+			return false
+		}
+	}
+	return true
+}
+
+// parseDirective reads the directive whose bytes start at format[i], after its '%', as doPrintf
+// does: flags among '#', '0', '+', '-', ' '; a decimal width; '.' and a decimal precision (only if
+// a byte follows the '.'); the verb. It returns the verb (as an int; -1 if the format ends first,
+// Go's %!(NOVERB)), whether the directive is %#v or %#w (Go's sharpV), and the index after it.
+// ok is false where the model does not follow Go: a '*' width or precision, an argument index
+// '[', or a width or precision of more than 7 digits.
+func parseDirective(format string, i int) (int, bool, int, bool) {
+	var sharp bool
+	var phase int // 0: flags, 1: width, 2: precision
+	var n int     // digits read of the width or precision
+	for i < len(format) {
+		c := format[i]
+		if phase == 0 && c == '#' {
+			sharp = true
+			i++
+			continue
+		}
+		if phase == 0 && (c == '+' || c == '-' || c == '0' || c == ' ') {
+			i++
+			continue
+		}
+		if '0' <= c && c <= '9' {
+			if phase == 0 {
+				phase = 1
+				n = 1
+				i++
+				continue
+			}
+			if n >= 7 {
+				return 0, false, 0, false
+			}
+			n++
+			i++
+			continue
+		}
+		if phase < 2 && c == '.' && i+1 < len(format) {
+			phase = 2
+			n = 0
+			i++
+			continue
+		}
+		if c == '*' || c == '[' {
+			return 0, false, 0, false
+		}
+		return int(c), sharp && (c == 'v' || c == 'w'), i + 1, true
+	}
+	return -1, false, i, true
+}
+
+// visitKind: printValue of x by its kind, without its methods: the model follows it for the
+// integer and string kinds, which read no memory, and is not defined for the others.
+func visitKind(x any) {
+	if isStrKind(x) {
+		return
+	}
+	if isIntKind(x) {
+		return
+	}
+	notModelled()
+}
+
+// visitArg calls the methods of x that Go's printArg calls under the directive (verb, sharpV),
+// and nothing else; the output is not modelled.
+// callError calls e.Error() as printArg's handleMethods does. Go calls it under catchPanic, which
+// recovers a panic of the method and prints it ("%!v(PANIC=Error method: ...)"), then goes on; the
+// model does not follow that: it is stuck there (notModelled), never panicking where Go recovers.
+func callError(e error) {
+	defer func() {
+		if recover() != nil {
+			notModelled()
+		}
+	}()
+	e.Error()
+}
+
+// callString calls s.String(), as callError calls Error().
+func callString(s interface{ String() string }) {
+	defer func() {
+		if recover() != nil {
+			notModelled()
+		}
+	}()
+	s.String()
+}
+
+func visitArg(x any, verb byte, sharpV bool, wrapErrs bool) {
+	if x == nil {
+		return
+	}
+	if verb == 'T' || verb == 'p' {
+		return
+	}
+	if isBasic(x) {
+		return
+	}
+	if b, ok := x.([]byte); ok {
+		_ = string(b) // printArg's fmtBytes: reads b, calls no method, under every verb
+		return
+	}
+	if ss, ok := x.([]string); ok {
+		_ = joinStrings(ss) // printValue: reads the elements, calls no method, under every verb
+		return
+	}
+	if verb == 'w' {
+		if _, ok := x.(error); !ok || !wrapErrs {
+			visitKind(x)
+			return
+		}
+		verb = 'v'
+	}
+	if _, ok := x.(interface{ Format(State, rune) }); ok {
+		notModelled()
+	}
+	if sharpV {
+		if _, ok := x.(interface{ GoString() string }); ok {
+			notModelled()
+		}
+	} else if verb == 'v' || verb == 's' || verb == 'x' || verb == 'X' || verb == 'q' {
+		if e, ok := x.(error); ok {
+			callError(e)
+			return
+		}
+		if s, ok := x.(interface{ String() string }); ok {
+			if _, ok := x.(interface{ CanInterface() bool }); ok {
+				notModelled() // a reflect.Value, which printArg unwraps
+			}
+			callString(s)
+			return
+		}
+	}
+	visitKind(x)
+}
+
+// visitRest goes through the directives of format from index i, the arguments from argNum,
+// calling what Go calls of each argument (visitArg), and then of each argument left over (Go's
+// %!(EXTRA ...), under %v). Before each argument it appends arbitrary strings to b
+// (writeArbitrary): what Go's printer has appended to its buffer by then, which a method of the
+// argument can read through a slice of the buffer that a writer kept (Fprintf hands the buffer to
+// w.Write, and the pool hands the printer out again). It returns the indices of the arguments of
+// the %w directives, and whether it gave up at a directive the model does not follow, every
+// argument being inert.
+func visitRest(b *buffer, format string, i int, a []any, argNum int, wrapErrs bool) ([]int, bool) {
+	var wrapped []int
+	for i < len(format) {
+		if format[i] != '%' {
+			i++
+			continue
+		}
+		verb, sharpV, next, ok := parseDirective(format, i+1)
+		if !ok {
+			if allInert(a) {
+				return wrapped, true
+			}
+			notModelled()
+		}
+		i = next
+		if verb < 0 || verb == '%' {
+			continue
+		}
+		if argNum >= len(a) {
+			continue
+		}
+		if verb == 'w' {
+			wrapped = append(wrapped, argNum)
+		}
+		writeArbitrary(b)
+		visitArg(a[argNum], byte(verb), sharpV, wrapErrs)
+		argNum++
+	}
+	for argNum < len(a) {
+		writeArbitrary(b)
+		visitArg(a[argNum], 'v', false, wrapErrs)
+		argNum++
+	}
+	return wrapped, false
+}
+
+// writeArbitrary appends one or more arbitrary strings to b (chooseString), each with one
+// writeString: Go's printer appends to its buffer piece by piece, and as GooseLang's append chooses
+// a new capacity freely when it reallocates, these appends can leave b as Go's leaves its buffer,
+// in content, backing array and capacity.
+func writeArbitrary(b *buffer) {
+	b.writeString(chooseString())
+	for gomodel.Choose() {
+		b.writeString(chooseString())
+	}
+}
+
+// doPrintf appends the formatted string to b and returns the indices of the arguments of the %w
+// directives, and whether those are unknown (visitRest gave up). It formats as the trusted model of
+// Sprintf did before stage 1 of perennial#671, up to the first directive it does not format or
+// whose argument is not inert, and appends that prefix to b, which Go's printer has appended by
+// then, before any method call; from there visitRest makes the calls Go makes, with arbitrary
+// strings appended before each, and arbitrary strings end the output.
+func doPrintf(b *buffer, format string, a []any, wrapErrs bool) ([]int, bool) {
+	var out string
+	var argNum int
+	var i int
+	for i < len(format) {
+		if format[i] != '%' {
+			out += string([]byte{format[i]})
+			i++
+			continue
+		}
+		if i+1 < len(format) && format[i+1] == '%' {
+			out += "%"
+			i += 2
+			continue
+		}
+		if argNum < len(a) {
+			s, next, ok := formatSlice(format, i, a[argNum])
+			if ok {
+				out += s
+				argNum++
+				i = next
+				continue
+			}
+		}
+		if argNum < len(a) && inert(a[argNum]) {
+			s, next, ok := formatArg(format, i, a[argNum])
+			if ok {
+				out += s
+				argNum++
+				i = next
+				continue
+			}
+		}
+		b.writeString(out)
+		wrapped, unknown := visitRest(b, format, i, a, argNum, wrapErrs)
+		writeArbitrary(b)
+		return wrapped, unknown
+	}
+	b.writeString(out)
+	if argNum < len(a) {
+		wrapped, unknown := visitRest(b, format, i, a, argNum, wrapErrs)
+		writeArbitrary(b)
+		return wrapped, unknown
+	}
+	return nil, false
+}
+
+// errorfResult: the error errorf returns of the message s, the indices wrapped of the arguments
+// of its %w directives, and whether those are unknown (doPrintf's results): errors.New(s) when no
+// %w directive had an argument, a *wrapError holding the argument as an error (nil if it is not
+// one) when one had, a *wrapErrors holding those of the arguments that are errors when several
+// had (Go sorts and deduplicates them only after an argument index, which the model does not
+// follow: parseDirective refuses '['). Where doPrintf gave up on a directive it does not follow,
+// every argument being inert (none is an error), the error is any of the three, holding no error.
+func errorfResult(s string, wrapped []int, unknown bool, a []any) error {
+	if unknown {
+		n := gomodel.ChooseUint64()
+		if n == 0 {
+			return errors.New(s)
+		}
+		if n == 1 {
+			return &wrapError{msg: s}
+		}
+		return &wrapErrors{msg: s}
+	}
+	if len(wrapped) == 0 {
+		return errors.New(s)
+	}
+	if len(wrapped) == 1 {
+		w := &wrapError{msg: s}
+		w.err, _ = a[wrapped[0]].(error)
+		return w
+	}
+	var errs []error
+	for _, argNum := range wrapped {
+		if e, ok := a[argNum].(error); ok {
+			errs = append(errs, e)
+		}
+	}
+	return &wrapErrors{s, errs}
+}
```

### goose/model/overlay/log/log.go  (tier 0, go-model-overlay)

```diff
diff --git a/goose/model/overlay/log/log.go b/goose/model/overlay/log/log.go
new file mode 100644
index 000000000..7fcf5f23b
--- /dev/null
+++ b/goose/model/overlay/log/log.go
@@ -0,0 +1,69 @@
+// The Go models of log.Printf, log.Println and log's init function
+// (Perennial/Code/log.toml, [model]), spliced into log.go in place of the real
+// declarations; modelDiscard is an addition.
+
+package log
+
+import (
+	"fmt"
+	"internal/gomodel"
+)
+
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
+func Printf(format string, v ...any) {
+	if gomodel.Choose() {
+		fmt.Fprintf(modelDiscard{}, format, v...)
+	}
+}
+
+// MODEL: Println is Printf's model (see there) with fmt.Appendln(b, v...) in
+// place of Appendf: the model formats the arguments with fmt.Fprintln, which
+// runs the same newPrinter, doPrintln and free.
+func Println(v ...any) {
+	if gomodel.Choose() {
+		fmt.Fprintln(modelDiscard{}, v...)
+	}
+}
+
+// modelDiscard is the writer of the models above: Write accepts every byte
+// and does nothing, as io.Discard's.
+type modelDiscard struct{}
+
+func (modelDiscard) Write(p []byte) (int, error) {
+	return len(p), nil
+}
+
+// MODEL: log's init function stores a closure into
+// log/internal.DefaultOutput, the output of log/slog's default handler; it
+// cannot panic. log/slog and log/internal are not translated, so no execution
+// of the model reads that variable, and the model does nothing.
+//
+//gomodel:replace init.0 "internal.DefaultOutput = func(pc uintptr, data []byte) error {"
+func init() {
+}
```

### goose/model/overlay/syscall/prlimit.go  (tier 0, go-model-overlay)

```diff
diff --git a/goose/model/overlay/syscall/prlimit.go b/goose/model/overlay/syscall/prlimit.go
new file mode 100644
index 000000000..a0ab2f307
--- /dev/null
+++ b/goose/model/overlay/syscall/prlimit.go
@@ -0,0 +1,34 @@
+// The Go model of syscall.prlimit1 (Perennial/Code/syscall.toml, [model]),
+// spliced into zsyscall_linux_amd64.go (amd64 linux, the platform
+// Perennial translates) in place of the real declaration.
+
+package syscall
+
+import "internal/gomodel"
+
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
+func prlimit1(pid int, resource int, newlimit *Rlimit, old *Rlimit) (err error) {
+	if newlimit != nil {
+		_ = *newlimit
+	}
+	if old != nil && gomodel.Choose() {
+		old.Cur = gomodel.ChooseUint64()
+		old.Max = gomodel.ChooseUint64()
+	}
+	e1 := Errno(gomodel.ChooseUint64())
+	if e1 != 0 {
+		err = errnoErr(e1)
+	}
+	return
+}
```

### goose/util/model.go  (tier 0, translator)

```diff
diff --git a/goose/util/model.go b/goose/util/model.go
index e784e522c..953fdf2e3 100644
--- a/goose/util/model.go
+++ b/goose/util/model.go
@@ -1296,44 +1296,12 @@ func typeString(t types.Type) string {
 	return types.TypeString(t, func(p *types.Package) string { return p.Path() })
 }
 
-// sameSignature reports whether the model's type o of a replaced function,
-// method or variable keeps the real type r: their types are identical up to
-// the names of parameters and results (unnamedParams), and every parameter or
-// result the real signature names (not blank) keeps its name in the model, so
-// that a model cannot swap same-typed parameters (`func Index(a, b []byte)`
-// modelled as `func Index(b, a []byte)`). The model may name one the real
-// declaration leaves unnamed or blank, and names inside a parameter's or
-// result's func type (which no body sees) are free.
-func sameSignature(r, o types.Type) bool {
-	if typeString(unnamedParams(r)) != typeString(unnamedParams(o)) {
-		return false
-	}
-	rsig, ok1 := r.(*types.Signature)
-	osig, ok2 := o.(*types.Signature)
-	if !ok1 || !ok2 {
-		return true
-	}
-	namesKept := func(rt, ot *types.Tuple) bool {
-		for i := 0; i < rt.Len(); i++ {
-			if n := rt.At(i).Name(); n != "" && n != "_" && ot.At(i).Name() != n {
-				return false
-			}
-		}
-		return true
-	}
-	return namesKept(rsig.Params(), osig.Params()) && namesKept(rsig.Results(), osig.Results())
-}
-
 // unnamedParams is t with the names of the parameters and results of its
 // function types dropped (in t and in the pointer, slice, array, map and
 // channel types it is built of), which types.Identical ignores too: a model
 // must name a parameter the real bodyless declaration leaves unnamed
-// (`func stopTimer(*Timer) bool`) to use it (sameSignature still compares the
-// names the real declaration gives). Everything else, variadic-ness and type
-// parameters included, is kept. A method's receiver is dropped, as
-// types.TypeString does not print it (the check of a replaced method compares
-// it separately); the receiver's type parameters stay bound to the real
-// receiver and print by name.
+// (`func stopTimer(*Timer) bool`) to use it. Everything else, variadic-ness
+// and type parameters included, is kept.
 func unnamedParams(t types.Type) types.Type {
 	switch t := t.(type) {
 	case *types.Signature:
@@ -1356,10 +1324,7 @@ func unnamedParams(t types.Type) types.Type {
 			}
 			return ps
 		}
-		// no receiver type parameters: go/types refuses them without a
-		// receiver ("function with receiver type parameters must have a
-		// receiver")
-		return types.NewSignatureType(nil, nil, tparams(t.TypeParams()),
+		return types.NewSignatureType(nil, tparams(t.RecvTypeParams()), tparams(t.TypeParams()),
 			strip(t.Params()), strip(t.Results()), t.Variadic())
 	case *types.Pointer:
 		return types.NewPointer(unnamedParams(t.Elem()))
@@ -1378,8 +1343,7 @@ func unnamedParams(t types.Type) types.Type {
 // CheckAPI checks that the overlaid package over keeps the API of the real
 // package real (D5): a replaced function, method or variable has an
 // identical type (printed with package paths, so type parameters keep their
-// names too; parameter and result names as sameSignature says); a replaced
-// type keeps its exported fields (names, order,
+// names too, and without parameter and result names, see unnamedParams); a replaced type keeps its exported fields (names, order,
 // types, embedding and tags, and the exported fields its embedded fields
 // promote), and an exported one also its kind (alias or defined, struct or
 // not), its underlying type if it is not a struct, and its comparability;
@@ -1417,7 +1381,7 @@ func CheckAPI(real, over *types.Package, config declfilter.ModelConfig) []error
 		}
 		switch r := r.(type) {
 		case *types.Func, *types.Var:
-			if !sameSignature(r.Type(), o.Type()) {
+			if typeString(unnamedParams(r.Type())) != typeString(unnamedParams(o.Type())) {
 				errs = append(errs, errors.Errorf("%s: type %s, which the model changes to %s",
 					name, typeString(r.Type()), typeString(o.Type())))
 			}
@@ -1460,7 +1424,7 @@ func CheckAPI(real, over *types.Package, config declfilter.ModelConfig) []error
 			continue
 		}
 		rr, or := typeString(rm.Signature().Recv().Type()), typeString(om.Signature().Recv().Type())
-		if rr != or || !sameSignature(rm.Type(), om.Type()) {
+		if rr != or || typeString(rm.Type()) != typeString(om.Type()) {
 			errs = append(errs, errors.Errorf("%s: (%s) %s, which the model changes to (%s) %s",
 				n, rr, typeString(rm.Type()), or, typeString(om.Type())))
 		}
@@ -1618,19 +1582,8 @@ func exportedFields(t types.Type) []string {
 	return out
 }
 
-// methodEntry is a method of a method set: its type, and where it is
-// declared (receiver and embedding path).
-type methodEntry struct {
-	typ   types.Type
-	where string
-}
-
-func (m methodEntry) String() string {
-	return typeString(m.typ) + " " + m.where
-}
-
-func methodSet(t types.Type) map[string]methodEntry {
-	ms := make(map[string]methodEntry)
+func methodSet(t types.Type) map[string]string {
+	ms := make(map[string]string)
 	set := types.NewMethodSet(t)
 	for i := range set.Len() {
 		sel := set.At(i)
@@ -1639,7 +1592,7 @@ func methodSet(t types.Type) map[string]methodEntry {
 		if r := f.Signature().Recv(); r != nil {
 			recv = typeString(r.Type())
 		}
-		ms[f.Name()] = methodEntry{f.Type(), fmt.Sprintf("(declared on %s, at embedding path %v)", recv, sel.Index())}
+		ms[f.Name()] = fmt.Sprintf("%s (declared on %s, at embedding path %v)", typeString(f.Type()), recv, sel.Index())
 	}
 	return ms
 }
@@ -1683,7 +1636,7 @@ func checkMethods(name string, r, o *types.TypeName, config declfilter.ModelConf
 					errs = append(errs, errors.Errorf("%s: the model adds the method %s to %s, "+
 						"which added_methods does not list", name, n, recv))
 				}
-			case rs.where != ovsig.where || !sameSignature(rs.typ, ovsig.typ):
+			case rs != ovsig:
 				errs = append(errs, errors.Errorf("%s: method %s of %s has type %s, which the model changes to %s",
 					name, n, recv, rs, ovsig))
 			}
```

### goose/util/model_test.go  (tier 0, translator)

```diff
diff --git a/goose/util/model_test.go b/goose/util/model_test.go
index 392a00754..a6c0fe63e 100644
--- a/goose/util/model_test.go
+++ b/goose/util/model_test.go
@@ -1,10 +1,6 @@
 package util
 
 import (
-	"go/ast"
-	"go/parser"
-	"go/token"
-	"go/types"
 	"os"
 	"os/exec"
 	"path/filepath"
@@ -205,73 +201,6 @@ func TestModelParamNames(t *testing.T) {
 	}
 }
 
-// TestModelParamNamesKept: a parameter or result the real declaration names
-// (not blank) keeps its name in the model, so same-typed parameters cannot be
-// swapped; a blank one may be named.
-func TestModelParamNamesKept(t *testing.T) {
-	real := "package p\n\nfunc Index(a, b []byte, _ int) (n int) { return 0 }\n"
-	for _, c := range []struct{ model, want string }{
-		{"func Index(a, b []byte, k int) (n int) { return k }", ""},
-		{"func Index(b, a []byte, _ int) (n int) { return len(a) }",
-			"Index: type func(a []byte, b []byte, _ int) (n int), which the model changes to " +
-				"func(b []byte, a []byte, _ int) (n int)"},
-		{"func Index(a, c []byte, _ int) (n int) { return 0 }", "which the model changes to"},
-		{"func Index(a, b []byte, _ int) (m int) { return 0 }", "which the model changes to"},
-		{"func Index(a, b []byte, _ int) int { return 0 }", "which the model changes to"},
-	} {
-		root := modelModule(t, real, "package p\n\n"+c.model+"\n",
-			"[model]\ndir = \"model\"\nreplaces = [\"Index\"]\n", nil)
-		_, err := buildModels(root, "./p")
-		switch {
-		case c.want == "" && err != nil:
-			t.Errorf("%s: %v", c.model, err)
-		case c.want != "" && (err == nil || !strings.Contains(err.Error(), c.want)):
-			t.Errorf("%s: error %v, want it to contain %q", c.model, err, c.want)
-		}
-	}
-}
-
-// TestModelGenericMethod: a replaced method of a generic type is checked like
-// a function (no go/types panic over its receiver's type parameters): a
-// parameter the real method leaves unnamed may be named, named ones keep
-// their names, and the types are compared.
-func TestModelGenericMethod(t *testing.T) {
-	real := "package p\n\ntype G[T any] struct{ x T }\n\n" +
-		"func (g *G[T]) M(a, b T, _ *T) T { return a }\n\nfunc (g *G[T]) N(T) {}\n"
-	for _, c := range []struct{ model, want string }{
-		{"func (g *G[T]) M(a, b T, p *T) T { return b }\n\nfunc (g *G[T]) N(v T) { g.x = v }", ""},
-		{"func (g *G[T]) M(b, a T, _ *T) T { return a }\n\nfunc (g *G[T]) N(T) {}",
-			"G.M: (*m/p.G[T]) func(a T, b T, _ *T) T, which the model changes to (*m/p.G[T]) func(b T, a T, _ *T) T"},
-		{"func (g *G[T]) M(a, b T, _ *T) T { return a }\n\nfunc (g *G[T]) N(v *T) {}",
-			"G.N: (*m/p.G[T]) func(T), which the model changes to (*m/p.G[T]) func(v *T)"},
-	} {
-		root := modelModule(t, real, "package p\n\n"+c.model+"\n",
-			"[model]\ndir = \"model\"\nreplaces = [\"G.M\", \"G.N\"]\n", nil)
-		_, err := buildModels(root, "./p")
-		switch {
-		case c.want == "" && err != nil:
-			t.Errorf("%s: %v", c.model, err)
-		case c.want != "" && (err == nil || !strings.Contains(err.Error(), c.want)):
-			t.Errorf("%s: error %v, want it to contain %q", c.model, err, c.want)
-		}
-	}
-	// unnamedParams of a generic type's method signature (receiver type
-	// parameters) does not panic and prints the parameters unnamed
-	fset := token.NewFileSet()
-	f, err := parser.ParseFile(fset, "p.go", real, 0)
-	if err != nil {
-		t.Fatal(err)
-	}
-	pkg, err := new(types.Config).Check("m/p", fset, []*ast.File{f}, nil)
-	if err != nil {
-		t.Fatal(err)
-	}
-	sig := method(pkg.Scope().Lookup("G").(*types.TypeName), "M").Type()
-	if s := typeString(unnamedParams(sig)); s != "func(T, T, *T) T" {
-		t.Errorf("unnamedParams: %s", s)
-	}
-}
-
 func TestModelErrors(t *testing.T) {
 	const real = `package p
 

```

(tiers 1-3 omitted; `--full` prints them, or `git diff` the files above)

