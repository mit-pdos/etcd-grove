<!-- Perennial goose-model-overlay-basic: etc/trusted-delta.py origin/lean..HEAD (go1.26.11), without its Diffs section (see git diff origin/lean..goose-model-overlay-basic in Perennial). -->
# Trust delta: range origin/lean..HEAD

## Files by tier

### tier 0 (TRUSTED)
- [D] Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.toml  (goose-config; +0 -3)
- [M] Perennial/Code/internal/bytealg.toml  (goose-config; +13 -18)
- [M] Perennial/Code/internal/gomodel.toml  (goose-config; +4 -3)
- [M] Perennial/Code/internal/sync.toml  (goose-config; +8 -14)
- [M] Perennial/Code/runtime.toml  (goose-config; +22 -7)
- [M] Perennial/Code/strings.toml  (goose-config; +9 -3)
- [M] Perennial/Code/sync.toml  (goose-config; +23 -29)
- [M] Perennial/Code/syscall.toml  (goose-config; +4 -0)
- [M] Perennial/Code/time.toml  (goose-config; +28 -26)
- [M] Perennial/Golang/Defn.lean  (semantics; +2 -7)
- [D] Perennial/Golang/Defn/Lock.lean  (semantics; +0 -39)
- [M] Perennial/TrustedCode/github_com/goose_lang/primitive.lean  (trusted-model; +39 -27)
- [D] Perennial/TrustedCode/internal/bytealg.lean  (trusted-model; +0 -81)
- [D] Perennial/TrustedCode/internal/sync.lean  (trusted-model; +0 -106)
- [M] Perennial/TrustedCode/runtime.lean  (trusted-model; +20 -176)
- [M] Perennial/TrustedCode/sync.lean  (trusted-model; +17 -157)
- [M] Perennial/TrustedCode/time.lean  (trusted-model; +51 -310)
- [A] goose/model/overlay/internal/bytealg/bytealg.go  (go-model-overlay; +39 -0)
- [A] goose/model/overlay/internal/bytealg/init.go  (go-model-overlay; +31 -0)
- [A] goose/model/overlay/internal/gomodel/choose.go  (go-model-overlay; +30 -0)
- [A] goose/model/overlay/internal/sync/mutex.go  (go-model-overlay; +66 -0)
- [A] goose/model/overlay/runtime/symtab.go  (go-model-overlay; +45 -0)
- [A] goose/model/overlay/runtime/traceback.go  (go-model-overlay; +37 -0)
- [M] goose/model/overlay/strings/strings.go  (go-model-overlay; +10 -4)
- [A] goose/model/overlay/sync/pool.go  (go-model-overlay; +107 -0)
- [A] goose/model/overlay/sync/runtime.go  (go-model-overlay; +141 -0)
- [A] goose/model/overlay/time/sleep.go  (go-model-overlay; +280 -0)
- [A] goose/model/overlay/time/tick.go  (go-model-overlay; +75 -0)
- [A] goose/model/overlay/time/time.go  (go-model-overlay; +46 -0)
- [A] goose/model/overlaytests/cond_test.go  (translator; +91 -0)
- [D] goose/model/pool/pool.go  (translator; +0 -50)
- [D] goose/model/pool/pool_test.go  (translator; +0 -53)
- [M] goose/util/model.go  (translator; +100 -2)
- [M] goose/util/model_asm_test.go  (translator; +24 -4)
- [A] goose/util/model_linkname_test.go  (translator; +62 -0)
- [M] goose/util/model_test.go  (translator; +26 -0)

### tier 1 (generated)
- [D] Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean  (generated-code; +0 -187)
- [M] Perennial/Code/internal/bytealg.lean  (generated-code; +99 -1)
- [M] Perennial/Code/internal/gomodel.lean  (generated-code; +80 -1)
- [M] Perennial/Code/internal/sync.lean  (generated-code; +154 -5)
- [M] Perennial/Code/runtime.lean  (generated-code; +4 -0)
- [M] Perennial/Code/runtime/chunk0.lean  (generated-code; +140 -1)
- [M] Perennial/Code/strings.lean  (generated-code; +13 -7)
- [M] Perennial/Code/sync.lean  (generated-code; +504 -1)
- [M] Perennial/Code/time.lean  (generated-code; +959 -10)
- [D] Perennial/GeneratedProof/github_com/mit_pdos/perennial/goose/model/pool.lean  (generated-proof; +0 -78)
- [M] Perennial/GeneratedProof/internal/bytealg.lean  (generated-proof; +0 -1)
- [M] Perennial/GeneratedProof/internal/sync.lean  (generated-proof; +59 -1)
- [M] Perennial/GeneratedProof/runtime.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk1.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk10.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk11.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk12.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk13.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk14.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk2.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk3.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk4.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk5.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk6.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk7.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk8.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/runtime/chunk9.lean  (generated-proof; +1 -0)
- [M] Perennial/GeneratedProof/sync.lean  (generated-proof; +58 -0)
- [M] Perennial/GeneratedProof/time.lean  (generated-proof; +2 -0)

### tier 2 (logic/libraries)
- [M] Perennial/Golang/Theory/Chan/AuSpec/ChanAuBase.lean  (logic; +2 -2)
- [M] Perennial/Golang/Theory/Chan/AuSpec/ChanAuNew.lean  (logic; +3 -3)
- [M] Perennial/Golang/Theory/Lock.lean  (logic; +34 -70)

### tier 3 (proofs, docs, tooling)
- [D] Perennial/ManualProof/internal/bytealg.lean  (other; +0 -5)
- [M] Perennial/Proof/context/Base.lean  (other; +1 -1)
- [M] Perennial/Proof/github_com/goose_lang/primitive/Base.lean  (other; +4 -4)
- [D] Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool.lean  (other; +0 -11)
- [D] Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Base.lean  (other; +0 -93)
- [D] Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Link.lean  (other; +0 -33)
- [D] Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Pool__Get.lean  (other; +0 -114)
- [D] Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Pool__Put.lean  (other; +0 -69)
- [M] Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/semantics/testMutexLiteral.lean  (other; +41 -24)
- [M] Perennial/Proof/internal/bytealg/Base.lean  (other; +1 -1)
- [M] Perennial/Proof/internal/bytealg/Link.lean  (other; +2 -2)
- [M] Perennial/Proof/internal/bytealg/MakeNoZero.lean  (other; +73 -62)
- [M] Perennial/Proof/internal/bytealg/initialize.lean  (other; +8 -4)
- [A] Perennial/Proof/internal/gomodel/Choose.lean  (other; +31 -0)
- [A] Perennial/Proof/internal/gomodel/ChooseString.lean  (other; +64 -0)
- [A] Perennial/Proof/internal/gomodel/ChooseStrings.lean  (other; +104 -0)
- [A] Perennial/Proof/internal/gomodel/ChooseUint64.lean  (other; +31 -0)
- [M] Perennial/Proof/internal/gomodel/Link.lean  (other; +16 -0)
- [M] Perennial/Proof/internal/sync/Base.lean  (other; +151 -4)
- [M] Perennial/Proof/internal/sync/Link.lean  (other; +6 -4)
- [M] Perennial/Proof/internal/sync/Mutex__Lock.lean  (other; +22 -5)
- [M] Perennial/Proof/internal/sync/Mutex__TryLock.lean  (other; +15 -10)
- [M] Perennial/Proof/internal/sync/Mutex__Unlock.lean  (other; +31 -4)
- [M] Perennial/Proof/internal/sync/initialize.lean  (other; +7 -1)
- [M] Perennial/Proof/runtime/Base.lean  (other; +1 -1)
- [M] Perennial/Proof/runtime/Frames__Next.lean  (other; +23 -19)
- [M] Perennial/Proof/runtime/Link.lean  (other; +3 -2)
- [M] Perennial/Proof/runtime/callers_.lean  (other; +17 -13)
- [M] Perennial/Proof/sync/Base.lean  (other; +2 -3)
- [M] Perennial/Proof/sync/CondDefs.lean  (other; +132 -4)
- [M] Perennial/Proof/sync/Cond__Broadcast.lean  (other; +1 -1)
- [M] Perennial/Proof/sync/Cond__Signal.lean  (other; +1 -1)
- [M] Perennial/Proof/sync/Cond__Wait.lean  (other; +1 -1)
- [M] Perennial/Proof/sync/Link.lean  (other; +18 -10)
- [M] Perennial/Proof/sync/NewCond.lean  (other; +4 -1)
- [M] Perennial/Proof/sync/PoolDefs.lean  (other; +69 -46)
- [M] Perennial/Proof/sync/Pool__Get.lean  (other; +120 -18)
- [M] Perennial/Proof/sync/Pool__Put.lean  (other; +39 -6)
- [M] Perennial/Proof/sync/Results.lean  (other; +1 -1)
- [M] Perennial/Proof/sync/initialize.lean  (other; +9 -4)
- [A] Perennial/Proof/sync/poolModelAt.lean  (other; +34 -0)
- [A] Perennial/Proof/sync/poolModelOf.lean  (other; +103 -0)
- [M] Perennial/Proof/sync/runtime_Semacquire.lean  (other; +43 -16)
- [M] Perennial/Proof/sync/runtime_SemacquireRWMutex.lean  (other; +12 -3)
- [M] Perennial/Proof/sync/runtime_SemacquireRWMutexR.lean  (other; +12 -3)
- [M] Perennial/Proof/sync/runtime_SemacquireWaitGroup.lean  (other; +12 -3)
- [M] Perennial/Proof/sync/runtime_Semrelease.lean  (other; +14 -7)
- [M] Perennial/Proof/sync/runtime_notifyListAdd.lean  (other; +10 -4)
- [M] Perennial/Proof/sync/runtime_notifyListNotifyAll.lean  (other; +32 -4)
- [M] Perennial/Proof/sync/runtime_notifyListNotifyOne.lean  (other; +32 -4)
- [M] Perennial/Proof/sync/runtime_notifyListWait.lean  (other; +23 -4)
- [M] Perennial/Proof/time/After.lean  (other; +58 -37)
- [M] Perennial/Proof/time/AfterFunc.lean  (other; +21 -19)
- [M] Perennial/Proof/time/Base.lean  (other; +90 -198)
- [M] Perennial/Proof/time/Link.lean  (other; +132 -36)
- [M] Perennial/Proof/time/NewTicker.lean  (other; +47 -28)
- [M] Perennial/Proof/time/NewTimer.lean  (other; +37 -27)
- [M] Perennial/Proof/time/Ticker__Reset.lean  (other; +16 -18)
- [M] Perennial/Proof/time/Ticker__Stop.lean  (other; +10 -9)
- [M] Perennial/Proof/time/Timer__Reset.lean  (other; +11 -7)
- [M] Perennial/Proof/time/Timer__Stop.lean  (other; +14 -8)
- [A] Perennial/Proof/time/checkWhen.lean  (other; +32 -0)
- [M] Perennial/Proof/time/initialize.lean  (other; +16 -13)
- [A] Perennial/Proof/time/makeTimerChan.lean  (other; +44 -0)
- [A] Perennial/Proof/time/newRuntimeTicker.lean  (other; +39 -0)
- [A] Perennial/Proof/time/newRuntimeTimer.lean  (other; +39 -0)
- [A] Perennial/Proof/time/newTimer_.lean  (other; +51 -0)
- [A] Perennial/Proof/time/nextWhen.lean  (other; +35 -0)
- [A] Perennial/Proof/time/now_.lean  (other; +33 -0)
- [A] Perennial/Proof/time/resetTimer.lean  (other; +35 -0)
- [A] Perennial/Proof/time/resetTimerAt.lean  (other; +49 -0)
- [A] Perennial/Proof/time/runtimeClockNow.lean  (other; +102 -0)
- [A] Perennial/Proof/time/runtimeClockWaitUntil.lean  (other; +41 -0)
- [M] Perennial/Proof/time/runtimeIsBubbled.lean  (other; +5 -2)
- [M] Perennial/Proof/time/runtimeNano.lean  (other; +8 -3)
- [M] Perennial/Proof/time/runtimeNow.lean  (other; +5 -4)
- [A] Perennial/Proof/time/runtimeTimerFire.lean  (other; +34 -0)
- [A] Perennial/Proof/time/sendTimes.lean  (other; +39 -0)
- [A] Perennial/Proof/time/sleepUntil.lean  (other; +41 -0)
- [A] Perennial/Proof/time/startTimer.lean  (other; +65 -0)
- [A] Perennial/Proof/time/stopTimer.lean  (other; +35 -0)
- [A] Perennial/Proof/time/stopTimerAt.lean  (other; +40 -0)
- [A] Perennial/Proof/time/timerFunc.lean  (other; +49 -0)
- [M] Perennial/Proof/time/when.lean  (other; +2 -1)
- [A] Perennial/Proof/time/whenAt.lean  (other; +37 -0)
- [D] Perennial/Spec/github_com/mit_pdos/perennial/goose/model/pool/Pool__Get.lean  (other; +0 -36)
- [D] Perennial/Spec/github_com/mit_pdos/perennial/goose/model/pool/Pool__Put.lean  (other; +0 -35)
- [A] Perennial/Spec/internal/gomodel/Choose.lean  (other; +32 -0)
- [A] Perennial/Spec/internal/gomodel/ChooseString.lean  (other; +32 -0)
- [A] Perennial/Spec/internal/gomodel/ChooseStrings.lean  (other; +33 -0)
- [A] Perennial/Spec/internal/gomodel/ChooseUint64.lean  (other; +32 -0)
- [M] Perennial/Spec/runtime/callers_.lean  (other; +1 -1)
- [A] Perennial/Spec/sync/poolModelAt.lean  (other; +35 -0)
- [A] Perennial/Spec/sync/poolModelOf.lean  (other; +35 -0)
- [M] Perennial/Spec/sync/runtime_notifyListAdd.lean  (other; +3 -3)
- [M] Perennial/Spec/sync/runtime_notifyListNotifyAll.lean  (other; +3 -3)
- [M] Perennial/Spec/sync/runtime_notifyListNotifyOne.lean  (other; +3 -3)
- [M] Perennial/Spec/sync/runtime_notifyListWait.lean  (other; +3 -3)
- [M] Perennial/Spec/time/After.lean  (other; +4 -2)
- [M] Perennial/Spec/time/AfterFunc.lean  (other; +4 -3)
- [M] Perennial/Spec/time/NewTicker.lean  (other; +3 -2)
- [M] Perennial/Spec/time/NewTimer.lean  (other; +3 -2)
- [A] Perennial/Spec/time/checkWhen.lean  (other; +33 -0)
- [A] Perennial/Spec/time/makeTimerChan.lean  (other; +33 -0)
- [A] Perennial/Spec/time/newRuntimeTicker.lean  (other; +35 -0)
- [A] Perennial/Spec/time/newRuntimeTimer.lean  (other; +35 -0)
- [A] Perennial/Spec/time/newTimer_.lean  (other; +38 -0)
- [A] Perennial/Spec/time/nextWhen.lean  (other; +32 -0)
- [A] Perennial/Spec/time/now_.lean  (other; +32 -0)
- [A] Perennial/Spec/time/resetTimer.lean  (other; +33 -0)
- [A] Perennial/Spec/time/resetTimerAt.lean  (other; +35 -0)
- [A] Perennial/Spec/time/runtimeClockNow.lean  (other; +34 -0)
- [A] Perennial/Spec/time/runtimeClockWaitUntil.lean  (other; +32 -0)
- [M] Perennial/Spec/time/runtimeIsBubbled.lean  (other; +2 -2)
- [M] Perennial/Spec/time/runtimeNano.lean  (other; +3 -3)
- [M] Perennial/Spec/time/runtimeNow.lean  (other; +2 -2)
- [A] Perennial/Spec/time/runtimeTimerFire.lean  (other; +34 -0)
- [A] Perennial/Spec/time/sendTimes.lean  (other; +37 -0)
- [A] Perennial/Spec/time/sleepUntil.lean  (other; +32 -0)
- [A] Perennial/Spec/time/startTimer.lean  (other; +33 -0)
- [A] Perennial/Spec/time/stopTimer.lean  (other; +33 -0)
- [A] Perennial/Spec/time/stopTimerAt.lean  (other; +32 -0)
- [A] Perennial/Spec/time/timerFunc.lean  (other; +34 -0)
- [M] Perennial/Spec/time/when.lean  (other; +2 -2)
- [A] Perennial/Spec/time/whenAt.lean  (other; +35 -0)
- [M] PerennialMeta.lean  (other; +0 -2)
- [M] README.md  (other; +14 -15)
- [M] docs/KNOWN_LIMITATIONS.md  (other; +46 -0)
- [M] docs/design/unsafe-memory.md  (other; +4 -4)
- [M] etc/model-tests.sh  (other; +36 -5)
- [M] etc/update-goose-new.py  (other; +0 -1)
- [M] goose/README.md  (other; +2 -1)
- [A] goose/model-overlays-plan.md  (other; +189 -0)
- [M] lakefile.toml  (other; +0 -2)

## Signals in changed lines

### Perennial/Code/internal/bytealg.toml  (tier 0, goose-config)
- `trusted-list` Perennial/Code/internal/bytealg.toml:23 (removed; old line): `trusted = ["MakeNoZero", "init.0"]`
- `model-replaces` Perennial/Code/internal/bytealg.toml:37: `replaces = ["IndexByte", "IndexByteString", "Index", "IndexString", "CompareString", "Count", "CountString",`
- `model-replaces` Perennial/Code/internal/bytealg.toml:43 (removed; old line): `replaces = ["IndexByte", "IndexByteString", "Index", "IndexString", "CompareString", "Count", "CountString"]`

### Perennial/Code/internal/gomodel.toml  (tier 0, goose-config)
- `trusted-list` Perennial/Code/internal/gomodel.toml:5 (removed; old line): `translate = ["!*"]`
- `trusted-list` Perennial/Code/internal/gomodel.toml:6: `translate = ["!*", "ChooseString", "ChooseStrings"]`

### Perennial/Code/internal/sync.toml  (tier 0, goose-config)
- `trusted-list` Perennial/Code/internal/sync.toml:1 (removed; old line): `translate = ["!*"]`
- `trusted-list` Perennial/Code/internal/sync.toml:4: `translate = ["!*", "Mutex", "mutexLocked"]`
- `trusted-list` Perennial/Code/internal/sync.toml:5 (removed; old line): `trusted = [`
- `model-table` Perennial/Code/internal/sync.toml:8: `[model]`
- `model-replaces` Perennial/Code/internal/sync.toml:10: `replaces = ["Mutex.Lock", "Mutex.TryLock", "Mutex.Unlock", "fatal"]`

### Perennial/Code/runtime.toml  (tier 0, goose-config)
- `trusted-list` Perennial/Code/runtime.toml:10 (removed; old line): `trusted = ["Gosched", "buildVersion", "callers", "Frames.Next"]`
- `trusted-list` Perennial/Code/runtime.toml:20: `trusted = ["Gosched", "callers", "buildVersion"]`
- `model-table` Perennial/Code/runtime.toml:26: `[model]`
- `model-replaces` Perennial/Code/runtime.toml:28: `replaces = ["Frames.Next"]`

### Perennial/Code/sync.toml  (tier 0, goose-config)
- `trusted-list` Perennial/Code/sync.toml:34 (removed; old line): `axiomatize = ["notifyList"]`
- `model-table` Perennial/Code/sync.toml:52: `[model]`
- `model-replaces` Perennial/Code/sync.toml:54: `replaces = [`

### Perennial/Code/time.toml  (tier 0, goose-config)
- `trusted-list` Perennial/Code/time.toml:2 (removed; old line): `trusted = [`
- `trusted-list` Perennial/Code/time.toml:6: `trusted = ["now", "Sleep", "newRuntimeTimer", "newRuntimeTicker", "runtimeTimerFire"]`
- `skip-list` Perennial/Code/time.toml:73: `[[skip]]`
- `model-table` Perennial/Code/time.toml:90: `[model]`
- `model-replaces` Perennial/Code/time.toml:92: `replaces = ["runtimeNow", "runtimeNano", "runtimeIsBubbled", "newTimer", "stopTimer", "resetTimer",`

### Perennial/Golang/Defn/Lock.lean  (tier 0, semantics)
- `set_option` Perennial/Golang/Defn/Lock.lean:19 (removed; old line): `set_option linter.iris.dupNamespace false in`
- `panic` Perennial/Golang/Defn/Lock.lean:32 (removed; old line): `else Panic "sync: unlock of unlocked mutex"`

### Perennial/TrustedCode/github_com/goose_lang/primitive.lean  (tier 0, trusted-model)
- `trusted-impl` Perennial/TrustedCode/github_com/goose_lang/primitive.lean:26 (removed; old line): `def Assume.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/github_com/goose_lang/primitive.lean:32 (removed; old line): `def Assert.impl : val :=`
- `set_option` Perennial/TrustedCode/github_com/goose_lang/primitive.lean:32: `set_option linter.iris.dupNamespace false in`
- `panic` Perennial/TrustedCode/github_com/goose_lang/primitive.lean:34 (removed; old line): `else Panic "assert failed"`
- `trusted-impl` Perennial/TrustedCode/github_com/goose_lang/primitive.lean:38 (removed; old line): `def Exit.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/github_com/goose_lang/primitive.lean:44 (removed; old line): `def Sleep.impl : val := λ: "duration", #()`
- `panic` Perennial/TrustedCode/github_com/goose_lang/primitive.lean:45: `else Panic "sync: unlock of unlocked mutex"`
- `trusted-impl` Perennial/TrustedCode/github_com/goose_lang/primitive.lean:46 (removed; old line): `def TimeNow.impl : val := λ: <>, ArbitraryInt`
- `trusted-impl` Perennial/TrustedCode/github_com/goose_lang/primitive.lean:48 (removed; old line): `def AfterFunc.impl : val := λ: "duration" "f", Fork "f" ;; Alloc "f"`
- `trusted-impl` Perennial/TrustedCode/github_com/goose_lang/primitive.lean:62: `def Assume.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/github_com/goose_lang/primitive.lean:64 (removed; old line): `def ResolveProph.impl : val := λ: "p" "val", ResolveProph (Var "p") (Var "val")`
- `trusted-impl` Perennial/TrustedCode/github_com/goose_lang/primitive.lean:72 (removed; old line): `def Linearize.impl : val := λ: <>, #()`

### Perennial/TrustedCode/internal/bytealg.lean  (tier 0, trusted-model)
- `set_option` Perennial/TrustedCode/internal/bytealg.lean:10 (removed; old line): `set_option linter.iris.style.nameCheck false`
- `trusted-impl` Perennial/TrustedCode/internal/bytealg.lean:51 (removed; old line): `noncomputable def MakeNoZero.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/internal/bytealg.lean:73 (removed; old line): `noncomputable def init.«0».impl : val :=`
- `global-var-addr` Perennial/TrustedCode/internal/bytealg.lean:75 (removed; old line): `(GlobalVarAddr go!"internal/bytealg.MaxLen" #())`

### Perennial/TrustedCode/internal/sync.lean  (tier 0, trusted-model)
- `set_option` Perennial/TrustedCode/internal/sync.lean:28 (removed; old line): `set_option linter.iris.style.nameCheck false`
- `trusted-impl` Perennial/TrustedCode/internal/sync.lean:58 (removed; old line): `def Mutex.TryLock.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/internal/sync.lean:73 (removed; old line): `def Mutex.Lock.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/internal/sync.lean:96 (removed; old line): `def Mutex.Unlock.impl : val :=`

### Perennial/TrustedCode/runtime.lean  (tier 0, trusted-model)
- `trusted-impl` Perennial/TrustedCode/runtime.lean:190 (removed; old line): `noncomputable def Frames.Next.impl : val :=`

### Perennial/TrustedCode/sync.lean  (tier 0, trusted-model)
- `trusted-impl` Perennial/TrustedCode/sync.lean:24 (removed; old line): `def runtime_notifyListAdd.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/sync.lean:26 (removed; old line): `def runtime_notifyListWait.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/sync.lean:28 (removed; old line): `def runtime_notifyListNotifyAll.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/sync.lean:30 (removed; old line): `def runtime_notifyListNotifyOne.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/sync.lean:31: `def poolModelAt.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/sync.lean:32 (removed; old line): `def runtime_notifyListCheck.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/sync.lean:46 (removed; old line): `def runtime_registerPoolCleanup.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/sync.lean:84 (removed; old line): `noncomputable def Pool.Put.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/sync.lean:115 (removed; old line): `noncomputable def Pool.Get.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/sync.lean:144 (removed; old line): `def runtime_Semacquire.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/sync.lean:159 (removed; old line): `def runtime_Semrelease.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/sync.lean:164 (removed; old line): `def runtime_SemacquireWaitGroup.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/sync.lean:167 (removed; old line): `def runtime_SemacquireRWMutexR.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/sync.lean:170 (removed; old line): `def runtime_SemacquireRWMutex.impl : val :=`

### Perennial/TrustedCode/time.lean  (tier 0, trusted-model)
- `trusted-impl` Perennial/TrustedCode/time.lean:28: `def now.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:35: `def Sleep.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:37 (removed; old line): `def stopTimer.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:45 (removed; old line): `def resetTimer.impl : val :=`
- `angelic` Perennial/TrustedCode/time.lean:48: ``AngelicExit` is then only on the model's own choice of address, the `alloc_struct` scheme) and`
- `trusted-impl` Perennial/TrustedCode/time.lean:58 (removed; old line): `def newTimer.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:67: `def newRuntimeTimer.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:71 (removed; old line): `def runtimeNano.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:78 (removed; old line): `def runtimeNow.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:79: `def newRuntimeTicker.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:83 (removed; old line): `def runtimeIsBubbled.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:86 (removed; old line): `def syncTimer.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:92: `def runtimeTimerFire.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:207 (removed; old line): `def After.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:219 (removed; old line): `def Sleep.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:241 (removed; old line): `def NewTimer.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:275 (removed; old line): `def NewTicker.impl : val :=`
- `panic` Perennial/TrustedCode/time.lean:277 (removed; old line): `if: "d" ≤⟨go.int64⟩ #(W64 0) then Panic "non-positive interval for NewTicker" else`
- `trusted-impl` Perennial/TrustedCode/time.lean:304 (removed; old line): `def Ticker.Stop.impl : val :=`
- `trusted-impl` Perennial/TrustedCode/time.lean:324 (removed; old line): `def Ticker.Reset.impl : val :=`
- `panic` Perennial/TrustedCode/time.lean:326 (removed; old line): `if: "d" ≤⟨go.int64⟩ #(W64 0) then Panic "non-positive interval for Ticker.Reset" else`
- `panic` Perennial/TrustedCode/time.lean:329 (removed; old line): `else Panic "time: Reset called on uninitialized Ticker"`

### goose/model/overlay/internal/bytealg/bytealg.go  (tier 0, go-model-overlay)
- `gomodel-choice` goose/model/overlay/internal/bytealg/bytealg.go:29: `c := int(gomodel.ChooseUint64() >> 1)`
- `gomodel-choice` goose/model/overlay/internal/bytealg/bytealg.go:36: `full[i] = byte(gomodel.ChooseUint64())`

### goose/model/overlay/internal/bytealg/init.go  (tier 0, go-model-overlay)
- `gomodel-replace` goose/model/overlay/internal/bytealg/init.go:24: `//gomodel:replace init.0 "if cpu.X86.HasAVX2 {"`
- `gomodel-choice` goose/model/overlay/internal/bytealg/init.go:26: `if gomodel.Choose() {`

### goose/model/overlay/internal/sync/mutex.go  (tier 0, go-model-overlay)
- `gomodel-choice` goose/model/overlay/internal/sync/mutex.go:43: `if gomodel.Choose() {`
- `gomodel-choice` goose/model/overlay/internal/sync/mutex.go:65: `gomodel.Stuck()`

### goose/model/overlay/runtime/symtab.go  (tier 0, go-model-overlay)
- `gomodel-choice` goose/model/overlay/runtime/symtab.go:34: `frame.PC = uintptr(gomodel.ChooseUint64())`
- `gomodel-choice` goose/model/overlay/runtime/symtab.go:35: `if gomodel.Choose() {`
- `gomodel-choice` goose/model/overlay/runtime/symtab.go:40: `frame.Line = int(gomodel.ChooseUint64())`
- `gomodel-choice` goose/model/overlay/runtime/symtab.go:41: `frame.startLine = int(gomodel.ChooseUint64())`
- `gomodel-choice` goose/model/overlay/runtime/symtab.go:42: `frame.Entry = uintptr(gomodel.ChooseUint64())`
- `gomodel-choice` goose/model/overlay/runtime/symtab.go:43: `more = gomodel.Choose()`

### goose/model/overlay/runtime/traceback.go  (tier 0, go-model-overlay)
- `gomodel-choice` goose/model/overlay/runtime/traceback.go:32: `for n < len(pcbuf) && n < 1<<40-1 && gomodel.Choose() {`
- `gomodel-choice` goose/model/overlay/runtime/traceback.go:33: `pcbuf[n] = uintptr(gomodel.ChooseUint64())`

### goose/model/overlay/sync/pool.go  (tier 0, go-model-overlay)
- `gomodel-choice` goose/model/overlay/sync/pool.go:67: `if gomodel.Choose() {`
- `gomodel-choice` goose/model/overlay/sync/pool.go:88: `if n != 0 && !gomodel.Choose() {`
- `gomodel-choice` goose/model/overlay/sync/pool.go:89: `i := gomodel.ChooseUint64() % n`

### goose/model/overlay/time/sleep.go  (tier 0, go-model-overlay)
- `gomodel-choice` goose/model/overlay/time/sleep.go:122: `if gomodel.Choose() {`
- `gomodel-choice` goose/model/overlay/time/sleep.go:138: `f(arg, uintptr(gomodel.ChooseUint64()), int64(gomodel.ChooseUint64()))`
- `gomodel-choice` goose/model/overlay/time/sleep.go:146: `gomodel.Stuck()`
- `gomodel-choice` goose/model/overlay/time/sleep.go:194: `return gomodel.Choose()`
- `gomodel-choice` goose/model/overlay/time/sleep.go:202: `return gomodel.Choose()`

### goose/model/overlay/time/time.go  (tier 0, go-model-overlay)
- `gomodel-choice` goose/model/overlay/time/time.go:45: `return gomodel.Choose()`

### Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean  (tier 1, generated-code)
- `set_option` Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean:10 (removed; old line): `set_option autoImplicit false`
- `set_option` Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean:11 (removed; old line): `set_option maxRecDepth 100000`
- `set_option` Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean:12 (removed; old line): `set_option maxHeartbeats 0`
- `set_option` Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean:13 (removed; old line): `set_option linter.all false`
- `set_option` Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean:14 (removed; old line): `set_option linter.deprecated true`
- `trusted-impl` Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean:34 (removed; old line): `noncomputable def Pool.Put.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean:64 (removed; old line): `noncomputable def Pool.Get.impl [GooseExts] [GoGlobalContext] : val :=`
- `step-rule` Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean:157 (removed; old line): `get_mu : ∀ (x : Pool), go.IsGoStepPureDetTagged under (StructFieldGet Pool.underlying go!"mu") #x (Val #(x.mu'))`
- `step-rule` Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean:158 (removed; old line): `set_mu : ∀ (x : Pool) (y : _root_.Perennial.github_com.goose_lang.primitive.Mutex), go.IsGoStepPureDetTagged under (StructFieldSet Pool.underlying go!"mu") (PairV #x #y) (Val #(({ x with mu' := y } : `
- `step-rule` Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean:159 (removed; old line): `get_items : ∀ (x : Pool), go.IsGoStepPureDetTagged under (StructFieldGet Pool.underlying go!"items") #x (Val #(x.items'))`
- `step-rule` Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean:160 (removed; old line): `set_items : ∀ (x : Pool) (y : GoSlice), go.IsGoStepPureDetTagged under (StructFieldSet Pool.underlying go!"items") (PairV #x #y) (Val #(({ x with items' := y } : Pool)))`
- `step-rule` Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean:163 (removed; old line): `ptr_Get_unfold : MethodUnfold (go.GoType.PointerType Pool.ty) go!"Get" Pool.Get.impl`
- `step-rule` Perennial/Code/github_com/mit_pdos/perennial/goose/model/pool.lean:164 (removed; old line): `ptr_Put_unfold : MethodUnfold (go.GoType.PointerType Pool.ty) go!"Put" Pool.Put.impl`

### Perennial/Code/internal/bytealg.lean  (tier 1, generated-code)
- `trusted-impl` Perennial/Code/internal/bytealg.lean:382: `noncomputable def MakeNoZero.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/internal/bytealg.lean:573: `noncomputable def init.«0».impl [GooseExts] [GoGlobalContext] : val :=`

### Perennial/Code/internal/gomodel.lean  (tier 1, generated-code)
- `trusted-impl` Perennial/Code/internal/gomodel.lean:49: `noncomputable def ChooseString.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/internal/gomodel.lean:80: `noncomputable def ChooseStrings.impl [GooseExts] [GoGlobalContext] : val :=`
- `step-rule` Perennial/Code/internal/gomodel.lean:124: `ChooseString_unfold : FuncUnfold ChooseString [] ChooseString.impl`
- `step-rule` Perennial/Code/internal/gomodel.lean:125: `ChooseStrings_unfold : FuncUnfold ChooseStrings [] ChooseStrings.impl`

### Perennial/Code/internal/sync.lean  (tier 1, generated-code)
- `opaque` Perennial/Code/internal/sync.lean:77 (removed; old line): `opaque mutexLocked [GooseExts] [GoGlobalContext] : val`
- `trusted-impl` Perennial/Code/internal/sync.lean:139: `noncomputable def Mutex.Lock.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/internal/sync.lean:164: `noncomputable def Mutex.TryLock.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/internal/sync.lean:199: `noncomputable def Mutex.Unlock.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/internal/sync.lean:220: `noncomputable def fatal.impl [GooseExts] [GoGlobalContext] : val :=`
- `step-rule` Perennial/Code/internal/sync.lean:381: `get_state : ∀ (x : Mutex), go.IsGoStepPureDetTagged under (StructFieldGet Mutex.underlying go!"state") #x (Val #(x.state'))`
- `step-rule` Perennial/Code/internal/sync.lean:382: `set_state : ∀ (x : Mutex) (y : w32), go.IsGoStepPureDetTagged under (StructFieldSet Mutex.underlying go!"state") (PairV #x #y) (Val #(({ x with state' := y } : Mutex)))`
- `step-rule` Perennial/Code/internal/sync.lean:383: `get_sema : ∀ (x : Mutex), go.IsGoStepPureDetTagged under (StructFieldGet Mutex.underlying go!"sema") #x (Val #(x.sema'))`
- `step-rule` Perennial/Code/internal/sync.lean:384: `set_sema : ∀ (x : Mutex) (y : w32), go.IsGoStepPureDetTagged under (StructFieldSet Mutex.underlying go!"sema") (PairV #x #y) (Val #(({ x with sema' := y } : Mutex)))`
- `step-rule` Perennial/Code/internal/sync.lean:411: `fatal_unfold : FuncUnfold fatal [] fatal.impl`

### Perennial/Code/runtime.lean  (tier 1, generated-code)
- `step-rule` Perennial/Code/runtime.lean:415: `callersModel_unfold : FuncUnfold callersModel [] callersModel.impl`

### Perennial/Code/runtime/chunk0.lean  (tier 1, generated-code)
- `trusted-impl` Perennial/Code/runtime/chunk0.lean:10727: `noncomputable def Frames.Next.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/runtime/chunk0.lean:10801: `noncomputable def callersModel.impl [GooseExts] [GoGlobalContext] : val :=`

### Perennial/Code/sync.lean  (tier 1, generated-code)
- `trusted-impl` Perennial/Code/sync.lean:773: `noncomputable def Pool.Put.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/sync.lean:821: `noncomputable def Pool.Get.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/sync.lean:898: `noncomputable def runtime_registerPoolCleanup.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/sync.lean:931: `noncomputable def runtime_Semacquire.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/sync.lean:965: `noncomputable def runtime_SemacquireWaitGroup.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/sync.lean:980: `noncomputable def runtime_SemacquireRWMutexR.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/sync.lean:996: `noncomputable def runtime_SemacquireRWMutex.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/sync.lean:1014: `noncomputable def runtime_Semrelease.impl [GooseExts] [GoGlobalContext] : val :=`
- `step-rule` Perennial/Code/sync.lean:2850: `get_mu : ∀ (x : poolModel), go.IsGoStepPureDetTagged under (StructFieldGet poolModel.underlying go!"mu") #x (Val #(x.mu'))`
- `step-rule` Perennial/Code/sync.lean:2851: `set_mu : ∀ (x : poolModel) (y : Mutex), go.IsGoStepPureDetTagged under (StructFieldSet poolModel.underlying go!"mu") (PairV #x #y) (Val #(({ x with mu' := y } : poolModel)))`
- `step-rule` Perennial/Code/sync.lean:2852: `get_items : ∀ (x : poolModel), go.IsGoStepPureDetTagged under (StructFieldGet poolModel.underlying go!"items") #x (Val #(x.items'))`
- `step-rule` Perennial/Code/sync.lean:2853: `set_items : ∀ (x : poolModel) (y : GoSlice), go.IsGoStepPureDetTagged under (StructFieldSet poolModel.underlying go!"items") (PairV #x #y) (Val #(({ x with items' := y } : poolModel)))`
- `step-rule` Perennial/Code/sync.lean:3015: `poolModelOf_unfold : FuncUnfold poolModelOf [] poolModelOf.impl`
- `step-rule` Perennial/Code/sync.lean:3016: `poolModelAt_unfold : FuncUnfold poolModelAt [] poolModelAt.impl`
- `trusted-impl`: ... and 6 more lines in this file

### Perennial/Code/time.lean  (tier 1, generated-code)
- `trusted-impl` Perennial/Code/time.lean:873: `noncomputable def newTimer.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/time.lean:926: `noncomputable def stopTimer.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/time.lean:947: `noncomputable def resetTimer.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/time.lean:1028: `noncomputable def NewTimer.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/time.lean:1127: `noncomputable def After.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/time.lean:1230: `noncomputable def NewTicker.impl [GooseExts] [GoGlobalContext] : val :=`
- `panic` Perennial/Code/time.lean:1284: `(App (App (Val (GoInstruction (FuncResolve go.panic []))) (Val #())) (Var "$a0"))))`
- `trusted-impl` Perennial/Code/time.lean:1300: `noncomputable def Ticker.Stop.impl [GooseExts] [GoGlobalContext] : val :=`
- `trusted-impl` Perennial/Code/time.lean:1330: `noncomputable def Ticker.Reset.impl [GooseExts] [GoGlobalContext] : val :=`
- `panic` Perennial/Code/time.lean:1347: `(App (App (Val (GoInstruction (FuncResolve go.panic []))) (Val #())) (Var "$a0"))))`
- `panic` Perennial/Code/time.lean:1353: `(App (App (Val (GoInstruction (FuncResolve go.panic []))) (Val #())) (Var "$a0"))))`
- `step-rule` Perennial/Code/time.lean:3111 (removed; old line): `syncTimer_unfold : FuncUnfold syncTimer [] syncTimer.impl`
- `step-rule` Perennial/Code/time.lean:4040: `now_unfold : FuncUnfold now [] now.impl`
- `step-rule` Perennial/Code/time.lean:4047: `makeTimerChan_unfold : FuncUnfold makeTimerChan [] makeTimerChan.impl`
- `step-rule` Perennial/Code/time.lean:4048: `sendTimes_unfold : FuncUnfold sendTimes [] sendTimes.impl`
- `step-rule` Perennial/Code/time.lean:4049: `timerFunc_unfold : FuncUnfold timerFunc [] timerFunc.impl`
- `step-rule` Perennial/Code/time.lean:4050: `checkWhen_unfold : FuncUnfold checkWhen [] checkWhen.impl`
- `step-rule` Perennial/Code/time.lean:4051: `startTimer_unfold : FuncUnfold startTimer [] startTimer.impl`
- `step-rule` Perennial/Code/time.lean:4052: `nextWhen_unfold : FuncUnfold nextWhen [] nextWhen.impl`
- `trusted-impl`: ... and 15 more lines in this file
- `step-rule`: ... and 9 more lines in this file

### Perennial/GeneratedProof/github_com/mit_pdos/perennial/goose/model/pool.lean  (tier 1, generated-proof)
- `set_option` Perennial/GeneratedProof/github_com/mit_pdos/perennial/goose/model/pool.lean:10 (removed; old line): `set_option autoImplicit false`
- `set_option` Perennial/GeneratedProof/github_com/mit_pdos/perennial/goose/model/pool.lean:11 (removed; old line): `set_option linter.all false`
- `set_option` Perennial/GeneratedProof/github_com/mit_pdos/perennial/goose/model/pool.lean:12 (removed; old line): `set_option linter.deprecated true`
- `extension` Perennial/GeneratedProof/github_com/mit_pdos/perennial/goose/model/pool.lean:22 (removed; old line): `variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]`

### Perennial/GeneratedProof/internal/sync.lean  (tier 1, generated-proof)
- `extension` Perennial/GeneratedProof/internal/sync.lean:138: `variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]`

### Perennial/GeneratedProof/sync.lean  (tier 1, generated-proof)
- `extension` Perennial/GeneratedProof/sync.lean:1049: `variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]`

### Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Base.lean  (tier 3, other)
- `extension` Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Base.lean:49 (removed; old line): `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Link.lean  (tier 3, other)
- `extension` Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Link.lean:19 (removed; old line): `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Pool__Get.lean  (tier 3, other)
- `set_option` Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Pool__Get.lean:13 (removed; old line): `set_option linter.iris.style.nameCheck false`
- `extension` Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Pool__Get.lean:22 (removed; old line): `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Pool__Put.lean  (tier 3, other)
- `set_option` Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Pool__Put.lean:13 (removed; old line): `set_option linter.iris.style.nameCheck false`
- `extension` Perennial/Proof/github_com/mit_pdos/perennial/goose/model/pool/Pool__Put.lean:22 (removed; old line): `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/internal/bytealg/MakeNoZero.lean  (tier 3, other)
- `extension` Perennial/Proof/internal/bytealg/MakeNoZero.lean:20 (removed; old line): `variable [GooseExts] [GooseSemantics] [GooseInterp]`
- `set_option` Perennial/Proof/internal/bytealg/MakeNoZero.lean:25 (removed; old line): `set_option maxHeartbeats 2000000 in`

### Perennial/Proof/internal/gomodel/Choose.lean  (tier 3, other)
- `extension` Perennial/Proof/internal/gomodel/Choose.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/internal/gomodel/ChooseString.lean  (tier 3, other)
- `extension` Perennial/Proof/internal/gomodel/ChooseString.lean:19: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/internal/gomodel/ChooseStrings.lean  (tier 3, other)
- `extension` Perennial/Proof/internal/gomodel/ChooseStrings.lean:19: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/internal/gomodel/ChooseUint64.lean  (tier 3, other)
- `extension` Perennial/Proof/internal/gomodel/ChooseUint64.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/internal/sync/Base.lean  (tier 3, other)
- `extension` Perennial/Proof/internal/sync/Base.lean:46: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/sync/CondDefs.lean  (tier 3, other)
- `extension` Perennial/Proof/sync/CondDefs.lean:103: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/sync/poolModelAt.lean  (tier 3, other)
- `set_option` Perennial/Proof/sync/poolModelAt.lean:10: `set_option linter.iris.style.nameCheck false`
- `extension` Perennial/Proof/sync/poolModelAt.lean:19: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/sync/poolModelOf.lean  (tier 3, other)
- `set_option` Perennial/Proof/sync/poolModelOf.lean:14: `set_option linter.iris.style.nameCheck false`
- `extension` Perennial/Proof/sync/poolModelOf.lean:23: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/Base.lean  (tier 3, other)
- `set_option` Perennial/Proof/time/Base.lean:125 (removed; old line): `set_option maxHeartbeats 1000000 in`
- `set_option` Perennial/Proof/time/Base.lean:259 (removed; old line): `set_option goose.wp.extras true in`

### Perennial/Proof/time/Link.lean  (tier 3, other)
- `extension` Perennial/Proof/time/Link.lean:168: `variable [GooseExts] [GooseSemantics] [GooseInterp]`
- `extension` Perennial/Proof/time/Link.lean:183: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/checkWhen.lean  (tier 3, other)
- `extension` Perennial/Proof/time/checkWhen.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/makeTimerChan.lean  (tier 3, other)
- `extension` Perennial/Proof/time/makeTimerChan.lean:18: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/newRuntimeTicker.lean  (tier 3, other)
- `extension` Perennial/Proof/time/newRuntimeTicker.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/newRuntimeTimer.lean  (tier 3, other)
- `extension` Perennial/Proof/time/newRuntimeTimer.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/newTimer_.lean  (tier 3, other)
- `extension` Perennial/Proof/time/newTimer_.lean:21: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/nextWhen.lean  (tier 3, other)
- `extension` Perennial/Proof/time/nextWhen.lean:18: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/now_.lean  (tier 3, other)
- `extension` Perennial/Proof/time/now_.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/resetTimer.lean  (tier 3, other)
- `extension` Perennial/Proof/time/resetTimer.lean:18: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/resetTimerAt.lean  (tier 3, other)
- `extension` Perennial/Proof/time/resetTimerAt.lean:21: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/runtimeClockNow.lean  (tier 3, other)
- `extension` Perennial/Proof/time/runtimeClockNow.lean:20: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/runtimeClockWaitUntil.lean  (tier 3, other)
- `extension` Perennial/Proof/time/runtimeClockWaitUntil.lean:19: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/runtimeTimerFire.lean  (tier 3, other)
- `extension` Perennial/Proof/time/runtimeTimerFire.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/sendTimes.lean  (tier 3, other)
- `extension` Perennial/Proof/time/sendTimes.lean:19: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/sleepUntil.lean  (tier 3, other)
- `extension` Perennial/Proof/time/sleepUntil.lean:19: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/startTimer.lean  (tier 3, other)
- `extension` Perennial/Proof/time/startTimer.lean:19: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/stopTimer.lean  (tier 3, other)
- `extension` Perennial/Proof/time/stopTimer.lean:18: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/stopTimerAt.lean  (tier 3, other)
- `extension` Perennial/Proof/time/stopTimerAt.lean:19: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/timerFunc.lean  (tier 3, other)
- `extension` Perennial/Proof/time/timerFunc.lean:18: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Proof/time/whenAt.lean  (tier 3, other)
- `extension` Perennial/Proof/time/whenAt.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/github_com/mit_pdos/perennial/goose/model/pool/Pool__Get.lean  (tier 3, other)
- `set_option` Perennial/Spec/github_com/mit_pdos/perennial/goose/model/pool/Pool__Get.lean:10 (removed; old line): `set_option linter.iris.style.nameCheck false`
- `extension` Perennial/Spec/github_com/mit_pdos/perennial/goose/model/pool/Pool__Get.lean:19 (removed; old line): `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/github_com/mit_pdos/perennial/goose/model/pool/Pool__Put.lean  (tier 3, other)
- `set_option` Perennial/Spec/github_com/mit_pdos/perennial/goose/model/pool/Pool__Put.lean:10 (removed; old line): `set_option linter.iris.style.nameCheck false`
- `extension` Perennial/Spec/github_com/mit_pdos/perennial/goose/model/pool/Pool__Put.lean:19 (removed; old line): `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/internal/gomodel/Choose.lean  (tier 3, other)
- `extension` Perennial/Spec/internal/gomodel/Choose.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/internal/gomodel/ChooseString.lean  (tier 3, other)
- `extension` Perennial/Spec/internal/gomodel/ChooseString.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/internal/gomodel/ChooseStrings.lean  (tier 3, other)
- `extension` Perennial/Spec/internal/gomodel/ChooseStrings.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/internal/gomodel/ChooseUint64.lean  (tier 3, other)
- `extension` Perennial/Spec/internal/gomodel/ChooseUint64.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/sync/poolModelAt.lean  (tier 3, other)
- `set_option` Perennial/Spec/sync/poolModelAt.lean:10: `set_option linter.iris.style.nameCheck false`
- `extension` Perennial/Spec/sync/poolModelAt.lean:19: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/sync/poolModelOf.lean  (tier 3, other)
- `set_option` Perennial/Spec/sync/poolModelOf.lean:10: `set_option linter.iris.style.nameCheck false`
- `extension` Perennial/Spec/sync/poolModelOf.lean:19: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/checkWhen.lean  (tier 3, other)
- `extension` Perennial/Spec/time/checkWhen.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/makeTimerChan.lean  (tier 3, other)
- `extension` Perennial/Spec/time/makeTimerChan.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/newRuntimeTicker.lean  (tier 3, other)
- `extension` Perennial/Spec/time/newRuntimeTicker.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/newRuntimeTimer.lean  (tier 3, other)
- `extension` Perennial/Spec/time/newRuntimeTimer.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/newTimer_.lean  (tier 3, other)
- `extension` Perennial/Spec/time/newTimer_.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/nextWhen.lean  (tier 3, other)
- `extension` Perennial/Spec/time/nextWhen.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/now_.lean  (tier 3, other)
- `extension` Perennial/Spec/time/now_.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/resetTimer.lean  (tier 3, other)
- `extension` Perennial/Spec/time/resetTimer.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/resetTimerAt.lean  (tier 3, other)
- `extension` Perennial/Spec/time/resetTimerAt.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/runtimeClockNow.lean  (tier 3, other)
- `extension` Perennial/Spec/time/runtimeClockNow.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/runtimeClockWaitUntil.lean  (tier 3, other)
- `extension` Perennial/Spec/time/runtimeClockWaitUntil.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/runtimeTimerFire.lean  (tier 3, other)
- `extension` Perennial/Spec/time/runtimeTimerFire.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/sendTimes.lean  (tier 3, other)
- `extension` Perennial/Spec/time/sendTimes.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/sleepUntil.lean  (tier 3, other)
- `extension` Perennial/Spec/time/sleepUntil.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/startTimer.lean  (tier 3, other)
- `extension` Perennial/Spec/time/startTimer.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/stopTimer.lean  (tier 3, other)
- `extension` Perennial/Spec/time/stopTimer.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/stopTimerAt.lean  (tier 3, other)
- `extension` Perennial/Spec/time/stopTimerAt.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/timerFunc.lean  (tier 3, other)
- `extension` Perennial/Spec/time/timerFunc.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

### Perennial/Spec/time/whenAt.lean  (tier 3, other)
- `extension` Perennial/Spec/time/whenAt.lean:17: `variable [GooseExts] [GooseSemantics] [GooseInterp]`

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

- Perennial/Code/internal/bytealg.toml `translate`: added ['MakeNoZero', 'init.0'], removed []
- Perennial/Code/internal/bytealg.toml `trusted`: added [], removed ['MakeNoZero', 'init.0']
- Perennial/Code/internal/gomodel.toml `translate`: added ['ChooseString', 'ChooseStrings'], removed []
- Perennial/Code/internal/sync.toml `imports`: added ['sync/atomic', 'internal/gomodel'], removed []
- Perennial/Code/internal/sync.toml `translate`: added ['Mutex', 'mutexLocked'], removed []
- Perennial/Code/internal/sync.toml `trusted`: added [], removed ['Mutex', 'Mutex.Lock', 'Mutex.TryLock', 'Mutex.Unlock']
- Perennial/Code/runtime.toml `imports`: added ['internal/gomodel'], removed []
- Perennial/Code/runtime.toml `trusted`: added [], removed ['Frames.Next']
- Perennial/Code/sync.toml `axiomatize`: added [], removed ['notifyList']
- Perennial/Code/sync.toml `imports`: added ['internal/gomodel'], removed []
- Perennial/Code/sync.toml `trusted`: added ['poolModelAt'], removed ['runtime_notifyList*', 'runtime_Semacquire*', 'runtime_Semrelease', 'runtime_registerPoolCleanup', 'Pool.Get', 'Pool.Put']
  - R2: `poolModelAt` must be justified by a goose run on the real source that fails on something irreducible (not a missing goose feature or semantics rule): move it to `translate` in a copy of the configuration and run `goose -configdir <copy> -dir goose sync` (SKILL.md, step 4)
- Perennial/Code/time.toml `imports`: added ['sync/atomic', 'internal/gomodel'], removed []
- Perennial/Code/time.toml `skip`: added ['asynctimerchan'], removed []
  - skipped `time.asynctimerchan`: reason: "`godebug.New("asynctimerchan")` (sleep.go): `internal/godebug` is not translated. Go's `New(name)` is
`return &Setting{name: name}`, an allocation, so the initializer cannot panic and has no effect beyond
the variable. Its only reader is `syncTimer`, which nothing in the model calls (`NewTimer`'s and
`NewTicker`'s models choose their channel's kind themselves), so no translated code reads the
unallocated variable.
"
    The reason must show that Go's initializer terminates, cannot panic and has no effect beyond the variable; read its callees (an effect on another variable or package, a registration, is not skippable).
    Go source (`go doc -u -src time.asynctimerchan`):

```go
package time // import "time"

var asynctimerchan = godebug.New("asynctimerchan")
```

- Perennial/Code/time.toml `trusted`: added ['now', 'newRuntimeTimer', 'newRuntimeTicker', 'runtimeTimerFire'], removed ['runtimeNano', 'newTimer', 'syncTimer', 'runtimeIsBubbled', 'runtimeNow', 'stopTimer', 'resetTimer', 'After', 'NewTimer', 'NewTicker', 'Ticker.Stop', 'Ticker.Reset', 'asynctimerchan']
  - R2: `now` must be justified by a goose run on the real source that fails on something irreducible (not a missing goose feature or semantics rule): move it to `translate` in a copy of the configuration and run `goose -configdir <copy> -dir goose time` (SKILL.md, step 4)
  - R2: `newRuntimeTimer` must be justified by a goose run on the real source that fails on something irreducible (not a missing goose feature or semantics rule): move it to `translate` in a copy of the configuration and run `goose -configdir <copy> -dir goose time` (SKILL.md, step 4)
  - R2: `newRuntimeTicker` must be justified by a goose run on the real source that fails on something irreducible (not a missing goose feature or semantics rule): move it to `translate` in a copy of the configuration and run `goose -configdir <copy> -dir goose time` (SKILL.md, step 4)
  - R2: `runtimeTimerFire` must be justified by a goose run on the real source that fails on something irreducible (not a missing goose feature or semantics rule): move it to `translate` in a copy of the configuration and run `goose -configdir <copy> -dir goose time` (SKILL.md, step 4)

A declaration that is neither translated nor trusted is axiomatized (name and type only). A `!pattern` in `translate` with the same name in `trusted` replaces goose's translation by a hand-written model: ask why the real translation is not used.

## Skipped package variables in generated code (TRUSTED)

Each entry of a `skipped'` list is a trusted claim (not running the variable's Go initializer is unobservable; rule R11): check every added or changed one against its Go declaration and its reason.

### Perennial/Code/time.lean

- added `time.asynctimerchan`
  - reason: '`godebug.New("asynctimerchan")` (sleep.go): `internal/godebug` is not translated. Go\'s `New(name)` is\n`return &Setting{name: name}`, an allocation, so the initializer cannot panic and has no effect beyond\nthe variable. Its only reader is `syncTimer`, which nothing in the model calls (`NewTimer`\'s and\n`NewTicker`\'s models choose their channel\'s kind themselves), so no translated code reads the\nunallocated variable.\n'
  - decl: 'var asynctimerchan = godebug.New("asynctimerchan")'

## Go model overlays (TRUSTED: model Go is reviewed as Go, rule R12)

For each replaced declaration: every behaviour of the real one (gc, linux/amd64, the pinned Go), under every use by the program and the real package, must be a behaviour of the model's translation. Compare the two sources line by line; every `gomodel.Choose`/`ChooseUint64`/`Stuck` needs a reason in the doc comment.

### Perennial/Code/internal/bytealg.toml  (package `internal/bytealg`)

- `[model]` before: dir = 'goose/model/overlay/internal/bytealg', replaces = ['IndexByte', 'IndexByteString', 'Index', 'IndexString', 'CompareString', 'Count', 'CountString'], added_methods = []
- `[model]` after:  dir = 'goose/model/overlay/internal/bytealg', replaces = ['IndexByte', 'IndexByteString', 'Index', 'IndexString', 'CompareString', 'Count', 'CountString', 'MakeNoZero', 'init.0'], added_methods = []
- model files: goose/model/overlay/internal/bytealg/bytealg.go, goose/model/overlay/internal/bytealg/compare_native.go, goose/model/overlay/internal/bytealg/count.go, goose/model/overlay/internal/bytealg/index.go, goose/model/overlay/internal/bytealg/indexbyte.go, goose/model/overlay/internal/bytealg/init.go; changed: goose/model/overlay/internal/bytealg/bytealg.go, goose/model/overlay/internal/bytealg/init.go

#### `internal/bytealg.MakeNoZero` (new)

Model (goose/model/overlay/internal/bytealg/bytealg.go:8):

```go
// MODEL: MakeNoZero(n) is a slice of length n and capacity at least n whose
// bytes, up to the capacity, are not zeroed. Go's has no Go body (goose:
// "external function"): the runtime defines it (runtime/slice.go,
// `//go:linkname bytealg_MakeNoZero internal/bytealg.MakeNoZero`, which the
// overlay blanks so that gc links this body instead) as
//
//	if uintptr(len) > maxAlloc {
//		panicmakeslicelen()
//	}
//	cap := roundupsize(uintptr(len), true)
//	return unsafe.Slice((*byte)(mallocgc(cap, nil, false)), cap)[:len]
//
// The model chooses the capacity (gomodel.ChooseUint64: any c >= n, which
// includes the size class roundupsize rounds n up to) and each byte up to the
// capacity (gomodel.ChooseUint64: mallocgc with needzero false returns memory
// with whatever it held, which a Go program cannot predict). A negative n
// panics in make with Go's message ("makeslice: len out of range"). An n
// above maxAlloc (2^48), where gc panics, is not checked: the model
// allocates, as the semantics' make and append do (docs/KNOWN_LIMITATIONS.md,
// "No limit on allocation size", which names MakeNoZero).
func MakeNoZero(n int) []byte {
	c := int(gomodel.ChooseUint64() >> 1)
	if c < n {
		c = n
	}
	b := make([]byte, n, c)
	full := b[:cap(b)]
	for i := range full {
		full[i] = byte(gomodel.ChooseUint64())
	}
	return b
}
```

Real (`go doc -u -src internal/bytealg.MakeNoZero`):

```go
package bytealg // import "internal/bytealg"

// MakeNoZero makes a slice of length n and capacity of at least n Bytes
// without zeroing the bytes (including the bytes between len and cap).
// It is the caller's responsibility to ensure uninitialized bytes
// do not leak to the end user.
func MakeNoZero(n int) []byte
```

#### `internal/bytealg.init.0` (new)

Model (goose/model/overlay/internal/bytealg/init.go:9):

```go
// MODEL: the package's init sets MaxLen to 63 or to 31. Go's
//
//	if cpu.X86.HasAVX2 {
//		MaxLen = 63
//	} else {
//		MaxLen = 31
//	}
//
// reads internal/cpu.X86, which no Go package initializer sets: the runtime
// fills it (cpu.Initialize, from schedinit) from the processor's cpuid
// (assembly) before any package is initialized. Goose translates the real
// init, but X86 would then stay zero and MaxLen always 31, more defined than
// gc. The model chooses (gomodel.Choose: the processor's AVX2 bit, which the
// semantics does not model) either value.
//
//gomodel:replace init.0 "if cpu.X86.HasAVX2 {"
func init() {
	if gomodel.Choose() {
		MaxLen = 63
	} else {
		MaxLen = 31
	}
}
```

(`go doc` cannot show `init.0`, the real package's init of that number in goose's numbering: read it in the real source. The marker quotes its first body line: "if cpu.X86.HasAVX2 {")

Replaced, unchanged: `CompareString`, `Count`, `CountString`, `Index`, `IndexByte`, `IndexByteString`, `IndexString`

### Perennial/Code/internal/gomodel.toml  (package `internal/gomodel`)

- `[model]` (unchanged): dir = 'goose/model/overlay/internal/gomodel', replaces = ['*'], added_methods = []
- model files: goose/model/overlay/internal/gomodel/choose.go, goose/model/overlay/internal/gomodel/gomodel.go; changed: goose/model/overlay/internal/gomodel/choose.go
- whole-package model (`replaces = ["*"]`): every real file is dropped; every model declaration that is not a primitive stub carries the R12 claim against the real declaration of the same name, if any

#### `internal/gomodel.ChooseString` (new)

Model (goose/model/overlay/internal/gomodel/choose.go:3):

```go
// ChooseString is an arbitrary string: every string is a result (and the loop
// may also not terminate). It is translated Go over Choose and ChooseUint64,
// not a primitive: a model uses it where Go's value is outside what the model
// tracks (a linker-set string, a symbol name, a command-line argument). In Go
// it is "".
func ChooseString() string {
	var b []byte
	for Choose() {
		b = append(b, byte(ChooseUint64()))
	}
	return string(b)
}
```

NOTE: the doc comment does not start with `MODEL:` (R12).

(no real declaration found by `go doc`: a model-only helper, or an added package)

#### `internal/gomodel.ChooseStrings` (new)

Model (goose/model/overlay/internal/gomodel/choose.go:16):

```go
// ChooseStrings is an arbitrary []string (nil or not, of any length, every
// element any string; in particular both nil and a non-nil empty slice: Go's
// os.runtime_args and syscall.runtime_envs return append([]string{}, ...),
// never nil). It is translated Go over Choose and ChooseString. In Go it is
// nil.
func ChooseStrings() []string {
	var a []string
	if Choose() {
		a = []string{}
	}
	for Choose() {
		a = append(a, ChooseString())
	}
	return a
}
```

NOTE: the doc comment does not start with `MODEL:` (R12).

(no real declaration found by `go doc`: a model-only helper, or an added package)

Additions (no claim of their own; a primitive stub carries the TrustedCode claim, R2; an added method must match `added_methods`):

- `Choose` (func, goose/model/overlay/internal/gomodel/gomodel.go:12, unchanged); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)
- `ChooseUint64` (func, goose/model/overlay/internal/gomodel/gomodel.go:17, unchanged); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)
- `Stuck` (func, goose/model/overlay/internal/gomodel/gomodel.go:22, unchanged); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)
- `StartRead` (func, goose/model/overlay/internal/gomodel/gomodel.go:33, unchanged); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)

### Perennial/Code/internal/sync.toml  (package `internal/sync`)

- `[model]` before: none
- `[model]` after:  dir = 'goose/model/overlay/internal/sync', replaces = ['Mutex.Lock', 'Mutex.TryLock', 'Mutex.Unlock', 'fatal'], added_methods = []
- model files: goose/model/overlay/internal/sync/mutex.go; changed: goose/model/overlay/internal/sync/mutex.go

#### `internal/sync.Mutex.Lock` (new)

Model (goose/model/overlay/internal/sync/mutex.go:13):

```go
// MODEL: Go's Lock is a compare-and-swap of state from 0 to mutexLocked, and
// on failure lockSlow, which spins and parks on the runtime's semaphore
// (runtime_SemacquireMutex, runtime_canSpin, runtime_doSpin,
// runtime_nanotime, all without a Go body) and records waiters, wakeups and
// starvation in state, read with plain loads that race with the
// compare-and-swaps. Goose translates lockSlow, but the hooks have no body and
// the racy reads are outside what the sequentially consistent semantics
// models; and the protocol in state is shared with TryLock and Unlock, so
// they are replaced together. The model keeps state at 0 (unlocked) or
// mutexLocked and spins on the fast path's compare-and-swap until it
// succeeds: Lock returns exactly when it takes the mutex, as in Go; a
// spinning model goroutine where Go's parks is a schedule with the same
// results (the model has no fairness and no starvation mode, which only
// order waiters). A goroutine that never gets the mutex spins forever where
// Go's parks forever: spinning for parking is partial correctness, and Go's
// deadlock detector (a global deadlock becomes the fatal throw "all
// goroutines are asleep") is not modelled (docs/KNOWN_LIMITATIONS.md).
func (m *Mutex) Lock() {
	for !atomic.CompareAndSwapInt32(&m.state, 0, mutexLocked) {
	}
}
```

Real (`go doc -u -src internal/sync.Mutex.Lock`):

```go
package sync // import "internal/sync"

// Lock locks m.
//
// See package [sync.Mutex] documentation.
func (m *Mutex) Lock() {
	// Fast path: grab unlocked mutex.
	if atomic.CompareAndSwapInt32(&m.state, 0, mutexLocked) {
		if race.Enabled {
			race.Acquire(unsafe.Pointer(m))
		}
		return
	}
	// Slow path (outlined so that the fast path can be inlined)
	m.lockSlow()
}
```

#### `internal/sync.Mutex.TryLock` (new)

Model (goose/model/overlay/internal/sync/mutex.go:35):

```go
// MODEL: Go's TryLock returns false if state is locked or starving, or if its
// compare-and-swap of state to locked loses to a concurrent change, else
// true. The model's state has no starvation bit and no waiters, so where Go
// fails on an unlocked mutex (starvation mode, or a waiter changing state),
// the model fails by an arbitrary choice (gomodel.Choose); otherwise it is the
// compare-and-swap of 0 to mutexLocked. It thus returns false in every case
// Go does, and true only when it took the mutex, as in Go.
func (m *Mutex) TryLock() bool {
	if gomodel.Choose() {
		return false
	}
	return atomic.CompareAndSwapInt32(&m.state, 0, mutexLocked)
}
```

Real (`go doc -u -src internal/sync.Mutex.TryLock`):

```go
package sync // import "internal/sync"

// TryLock tries to lock m and reports whether it succeeded.
//
// See package [sync.Mutex] documentation.
func (m *Mutex) TryLock() bool {
	old := m.state
	if old&(mutexLocked|mutexStarving) != 0 {
		return false
	}

	// There may be a goroutine waiting for the mutex, but we are
	// running now and can try to grab the mutex before that
	// goroutine wakes up.
	if !atomic.CompareAndSwapInt32(&m.state, old, old|mutexLocked) {
		return false
	}

	if race.Enabled {
		race.Acquire(unsafe.Pointer(m))
	}
	return true
}
```

#### `internal/sync.Mutex.Unlock` (new)

Model (goose/model/overlay/internal/sync/mutex.go:49):

```go
// MODEL: Go's Unlock subtracts mutexLocked from state and, if waiters remain,
// wakes one (unlockSlow, through runtime_Semrelease); on an unlocked mutex it
// calls fatal("sync: unlock of unlocked mutex"). The model's state has no
// waiters (a spinning Lock sees the 0), so Unlock is the compare-and-swap of
// mutexLocked to 0, and fatal where it fails, that is where the mutex is not
// locked.
func (m *Mutex) Unlock() {
	if !atomic.CompareAndSwapInt32(&m.state, mutexLocked, 0) {
		fatal("sync: unlock of unlocked mutex")
	}
}
```

Real (`go doc -u -src internal/sync.Mutex.Unlock`):

```go
package sync // import "internal/sync"

// Unlock unlocks m.
//
// See package [sync.Mutex] documentation.
func (m *Mutex) Unlock() {
	if race.Enabled {
		_ = m.state
		race.Release(unsafe.Pointer(m))
	}

	// Fast path: drop lock bit.
	new := atomic.AddInt32(&m.state, -mutexLocked)
	if new != 0 {
		// Outlined slow path to allow inlining the fast path.
		// To hide unlockSlow during tracing we skip one extra frame when tracing GoUnblock.
		m.unlockSlow(new)
	}
}
```

#### `internal/sync.fatal` (new)

Model (goose/model/overlay/internal/sync/mutex.go:61):

```go
// MODEL: Go's fatal (a runtime push linkname, no Go body) prints the message
// and ends the program, and recover cannot catch it. The model has no
// behaviour there (gomodel.Stuck): a verified program never calls it.
func fatal(string) {
	gomodel.Stuck()
}
```

Real (`go doc -u -src internal/sync.fatal`):

```go
package sync // import "internal/sync"

//go:linkname fatal
func fatal(string)
```

### Perennial/Code/runtime.toml  (package `runtime`)

- `[model]` before: none
- `[model]` after:  dir = 'goose/model/overlay/runtime', replaces = ['Frames.Next'], added_methods = []
- model files: goose/model/overlay/runtime/symtab.go, goose/model/overlay/runtime/traceback.go; changed: goose/model/overlay/runtime/symtab.go, goose/model/overlay/runtime/traceback.go

#### `runtime.Frames.Next` (new)

Model (goose/model/overlay/runtime/symtab.go:8):

```go
// MODEL: ci.Next() is the next frame of the program counters ci.callers,
// symbolized through the binary's tables (findfunc, the inlining tree, the
// cgo symbolizer; goose: "inc or dec statement with unsupported type
// uintptr", symtab.go:131), and whether another one follows. Go reads and
// writes *ci, so a nil ci panics (nil dereference) and a concurrent call on
// the same Frames races; the model's load and store of ci.callers do both.
// The model stores ci.callers on every call, also on an exhausted Frames,
// where Go only reads *ci: two concurrent Next calls on an exhausted Frames
// race in the model and not in Go (extra behaviour, the safe direction: a
// race is stuck in GooseLang, so a proof must exclude it). The model leaves *ci unchanged, where Go advances it, which no caller
// observes (the fields are unexported). It does not read the words
// ci.callers points to, which Go does (ci.callers[0]): a concurrent write to
// them races in Go and not in the model, but Go reads them only to look them
// up (any value gives some frames, a garbage one is skipped), and the model's
// frames are arbitrary anyway, so no outcome of that race is missing.
// Every exported field of the frame and more is arbitrary, a superset of
// what Go returns (goose/model/runtime/callers_test.go: a nil Func for a frame
// of a function inlined into its caller, Function/File/Line of the call
// sites, the zero frame with more false once the frames are exhausted). A
// non-nil Func is new(Func): Func is zero-size, and the semantics allocates a
// zero-size value at an arbitrary non-null address that owns no memory, so
// two results can be equal or not and a proof can read nothing through it, as
// with Go's pointers into the binary's tables. startLine and Entry are
// arbitrary too; funcInfo stays zero (unexported, read only by the runtime).
func (ci *Frames) Next() (frame Frame, more bool) {
	ci.callers = ci.callers
	frame.PC = uintptr(gomodel.ChooseUint64())
	if gomodel.Choose() {
		frame.Func = new(Func)
	}
	frame.Function = gomodel.ChooseString()
	frame.File = gomodel.ChooseString()
	frame.Line = int(gomodel.ChooseUint64())
	frame.startLine = int(gomodel.ChooseUint64())
	frame.Entry = uintptr(gomodel.ChooseUint64())
	more = gomodel.Choose()
	return
}
```

Real (`go doc -u -src runtime.Frames.Next`):

```go
package runtime // import "runtime"

// Next returns a [Frame] representing the next call frame in the slice
// of PC values. If it has already returned all call frames, Next
// returns a zero [Frame].
//
// The more result indicates whether the next call to Next will return
// a valid [Frame]. It does not necessarily indicate whether this call
// returned one.
//
// See the [Frames] example for idiomatic usage.
func (ci *Frames) Next() (frame Frame, more bool) {
	for len(ci.frames) < 2 {
		// Find the next frame.
		// We need to look for 2 frames so we know what
		// to return for the "more" result.
		if len(ci.callers) == 0 {
			break
		}
		var pc uintptr
		if ci.nextPC != 0 {
			pc, ci.nextPC = ci.nextPC, 0
		} else {
			pc, ci.callers = ci.callers[0], ci.callers[1:]
		}
		funcInfo := findfunc(pc)
		if !funcInfo.valid() {
			if cgoSymbolizerAvailable() {
				// Pre-expand cgo frames. We could do this
				// incrementally, too, but there's no way to
				// avoid allocation in this case anyway.
				ci.frames = append(ci.frames, expandCgoFrames(pc)...)
			}
			continue
		}
		f := funcInfo._Func()
		entry := f.Entry()
		// We store the pc of the start of the instruction following
		// the instruction in question (the call or the inline mark).
		// This is done for historical reasons, and to make FuncForPC
		// work correctly for entries in the result of runtime.Callers.
		// Decrement to get back to the instruction we care about.
		//
		// It is not possible to get pc == entry from runtime.Callers,
		// but if the caller does provide one, provide best-effort
		// results by avoiding backing out of the function entirely.
		if pc > entry {
			pc--
		}
		// It's important that interpret pc non-strictly as cgoTraceback may
		// have added bogus PCs with a valid funcInfo but invalid PCDATA.
		u, uf := newInlineUnwinder(funcInfo, pc)
		sf := u.srcFunc(uf)
		if u.isInlined(uf) {
			// Note: entry is not modified. It always refers to a real frame, not an inlined one.
			// File/line from funcline1 below are already correct.
			f = nil

			// When CallersFrame is invoked using the PC list returned by Callers,
			// the PC list includes virtual PCs corresponding to each outer frame
			// around an innermost real inlined PC.
			// We also want to support code passing in a PC list extracted from a
			// stack trace, and there only the real PCs are printed, not the virtual ones.
			// So check to see if the implied virtual PC for this PC (obtained from the
			// unwinder itself) is the next PC in ci.callers. If not, insert it.
			// The +1 here correspond to the pc-- above: the output of Callers
			// and therefore the input to CallersFrames is return PCs from the stack;
			// The pc-- backs up into the CALL instruction (not the first byte of the CALL
			// instruction, but good enough to find it nonetheless).
			// There are no cycles in implied virtual PCs (some number of frames were
			// inlined, but that number is finite), so this unpacking cannot cause an infinite loop.
			for unext := u.next(uf); unext.valid() && len(ci.callers) > 0 && ci.callers[0] != unext.pc+1; unext = u.next(unext) {
				snext := u.srcFunc(unext)
				if snext.funcID == abi.FuncIDWrapper && elideWrapperCalling(sf.funcID) {
					// Skip, because tracebackPCs (inside runtime.Callers) would too.
					continue
				}
				ci.nextPC = unext.pc + 1
				break
			}
... (38 more lines)
```

Additions (no claim of their own; a primitive stub carries the TrustedCode claim, R2; an added method must match `added_methods`):

- `callersModel` (func, goose/model/overlay/runtime/traceback.go:10, new)

### Perennial/Code/strings.toml  (package `strings`)

- `[model]` (unchanged): dir = 'goose/model/overlay/strings', replaces = ['Split', 'Builder.copyCheck', 'Builder.String', 'Builder.Reset', 'IndexRune'], added_methods = []
- model files: goose/model/overlay/strings/builder.go, goose/model/overlay/strings/strings.go; changed: goose/model/overlay/strings/strings.go

#### `strings.Split` (changed)

Model (goose/model/overlay/strings/strings.go:11):

```go
// MODEL: Split(s, sep) is the substrings of s between the occurrences of sep
// (found left to right, not overlapping), as Go's genSplit(s, sep, 0, -1)
// computes them. The model finds the occurrences by testing HasPrefix at each
// position, where Go's genSplit counts them with Count and finds them with
// Index. Goose translates the real Split, but at len(s) = 2^63-1 (a string gc
// cannot hold) genSplit's len(s)+1 overflows and it panics, so its spec would
// need a bound on len(s) that Split's spec does not have
// (Perennial/Code/strings.toml). The model returns the same fields as
// genSplit wherever genSplit does not panic, and there only: building such a
// string needs an allocation gc refuses, which the semantics allows
// (docs/KNOWN_LIMITATIONS.md, "No limit on allocation size"). For an empty
// sep, Go splits s into its UTF-8 sequences (explode); the model is stuck
// there, so every spec of Split requires sep to be non-empty.
func Split(s, sep string) []string {
	if len(sep) == 0 {
		gomodel.Stuck()
	}
	var a []string
	var field string
	rest := s
	for len(rest) > 0 {
		if HasPrefix(rest, sep) {
			a = append(a, field)
			field = ""
			rest = rest[len(sep):]
			continue
		}
		field += rest[:1]
		rest = rest[1:]
	}
	return append(a, field)
}
```

Real (`go doc -u -src strings.Split`):

```go
package strings // import "strings"

// Split slices s into all substrings separated by sep and returns a slice of
// the substrings between those separators.
//
// If s does not contain sep and sep is not empty, Split returns a
// slice of length 1 whose only element is s.
//
// If sep is empty, Split splits after each UTF-8 sequence. If both s
// and sep are empty, Split returns an empty slice.
//
// It is equivalent to [SplitN] with a count of -1.
//
// To split around the first instance of a separator, see [Cut].
func Split(s, sep string) []string { return genSplit(s, sep, 0, -1) }
```

Replaced, unchanged: `Builder.Reset`, `Builder.String`, `Builder.copyCheck`, `IndexRune`

### Perennial/Code/sync.toml  (package `sync`)

- `[model]` before: none
- `[model]` after:  dir = 'goose/model/overlay/sync', replaces = ['runtime_Semacquire', 'runtime_SemacquireWaitGroup', 'runtime_SemacquireRWMutexR', 'runtime_SemacquireRWMutex', 'runtime_Semrelease', 'runtime_notifyListAdd', 'runtime_notifyListWait', 'runtime_notifyListNotifyAll', 'runtime_notifyListNotifyOne', 'runtime_notifyListCheck', 'runtime_registerPoolCleanup', 'Pool.Get', 'Pool.Put'], added_methods = []
- model files: goose/model/overlay/sync/pool.go, goose/model/overlay/sync/runtime.go; changed: goose/model/overlay/sync/pool.go, goose/model/overlay/sync/runtime.go

#### `sync.Pool.Get` (new)

Model (goose/model/overlay/sync/pool.go:75):

```go
// MODEL: Go's Get pins the goroutine to its P and takes the P's private
// value, else pops its shared chain, else steals from other Ps and the
// victim cache (getSlow); if it found nothing and New is not nil, it returns
// New(). Goose translates it but is stuck as for Put. The model's search
// takes an arbitrary element of the pool's state or nothing, even when the
// state is not empty (gomodel.Choose: Go's search may miss values in other
// Ps' chains or dropped by the GC, and gomodel.ChooseUint64: which value it
// finds); the rest, calling New, is Go's.
func (p *Pool) Get() any {
	s := poolModelOf(p)
	var x any
	s.mu.Lock()
	n := uint64(len(s.items))
	if n != 0 && !gomodel.Choose() {
		i := gomodel.ChooseUint64() % n
		x = s.items[i]
		s.items[i] = s.items[n-1]
		s.items = s.items[:n-1]
	}
	s.mu.Unlock()
	if x == nil && p.New != nil {
		x = p.New()
	}
	return x
}
```

Real (`go doc -u -src sync.Pool.Get`):

```go
package sync // import "sync"

// Get selects an arbitrary item from the [Pool], removes it from the
// Pool, and returns it to the caller.
// Get may choose to ignore the pool and treat it as empty.
// Callers should not assume any relation between values passed to [Pool.Put] and
// the values returned by Get.
//
// If Get would otherwise return nil and p.New is non-nil, Get returns
// the result of calling p.New.
func (p *Pool) Get() any {
	if race.Enabled {
		race.Disable()
	}
	l, pid := p.pin()
	x := l.private
	l.private = nil
	if x == nil {
		// Try to pop the head of the local shard. We prefer
		// the head over the tail for temporal locality of
		// reuse.
		x, _ = l.shared.popHead()
		if x == nil {
			x = p.getSlow(pid)
		}
	}
	runtime_procUnpin()
	if race.Enabled {
		race.Enable()
		if x != nil {
			race.Acquire(poolRaceAddr(x))
		}
	}
	if x == nil && p.New != nil {
		x = p.New()
	}
	return x
}
```

#### `sync.Pool.Put` (new)

Model (goose/model/overlay/sync/pool.go:52):

```go
// MODEL: Go's Put ignores nil and otherwise pins the goroutine to its P and
// stores x in that P's private slot or pushes it onto the P's lock-free
// shared chain; the GC later moves the per-P pools to the victim cache and
// then drops them. Goose translates it, but the translation is stuck at
// indexLocal's conversion of a uintptr back to an unsafe.Pointer (pointer
// arithmetic) and at poolDequeue's store of an any through an
// unsafe.Pointer to its eface; runtime_procPin, which keeps the goroutine on
// its P, has no Go body. The model ignores nil as Go does, and otherwise
// adds x to the pool's state or drops it (gomodel.Choose: the GC may drop it
// in Go before any Get).
func (p *Pool) Put(x any) {
	if x == nil {
		return
	}
	s := poolModelOf(p)
	if gomodel.Choose() {
		return
	}
	s.mu.Lock()
	s.items = append(s.items, x)
	s.mu.Unlock()
}
```

Real (`go doc -u -src sync.Pool.Put`):

```go
package sync // import "sync"

// Put adds x to the pool.
func (p *Pool) Put(x any) {
	if x == nil {
		return
	}
	if race.Enabled {
		if runtime_randn(4) == 0 {
			// Randomly drop x on floor.
			return
		}
		race.ReleaseMerge(poolRaceAddr(x))
		race.Disable()
	}
	l, _ := p.pin()
	if l.private == nil {
		l.private = x
	} else {
		l.shared.pushHead(x)
	}
	runtime_procUnpin()
	if race.Enabled {
		race.Enable()
	}
}
```

#### `sync.runtime_Semacquire` (new)

Model (goose/model/overlay/sync/runtime.go:13):

```go
// MODEL: Go's runtime_Semacquire (runtime/sema.go, semacquire1) waits until
// *s > 0 and decrements it, trying first
//
//	func cansemacquire(addr *uint32) bool {
//		for {
//			v := atomic.Load(addr)
//			if v == 0 {
//				return false
//			}
//			if atomic.Cas(addr, v, v-1) {
//				return true
//			}
//		}
//	}
//
// and, while that fails, parking on a queue that runtime_Semrelease wakes. The
// model is cansemacquire's loop, retried until it succeeds: it returns exactly
// when it has decremented a positive *s, as Go's does; a model goroutine
// spinning where Go's parks is a schedule with the same results (the queue
// only orders the waiters). A goroutine that never acquires spins forever
// where Go's parks forever: spinning for parking is partial correctness, and
// Go's deadlock detector (a global deadlock becomes the fatal throw "all
// goroutines are asleep") is not modelled (docs/KNOWN_LIMITATIONS.md).
func runtime_Semacquire(s *uint32) {
	for {
		v := atomic.LoadUint32(s)
		if v == 0 {
			continue
		}
		if atomic.CompareAndSwapUint32(s, v, v-1) {
			return
		}
	}
}
```

Real (`go doc -u -src sync.runtime_Semacquire`):

```go
package sync // import "sync"

// Semacquire waits until *s > 0 and then atomically decrements it.
// It is intended as a simple sleep primitive for use by the synchronization
// library and should not be used directly.
func runtime_Semacquire(s *uint32)
```

#### `sync.runtime_SemacquireRWMutex` (new)

Model (goose/model/overlay/sync/runtime.go:61):

```go
// MODEL: as runtime_Semacquire (see runtime_SemacquireRWMutexR).
func runtime_SemacquireRWMutex(s *uint32, lifo bool, skipframes int) {
	runtime_Semacquire(s)
}
```

Real (`go doc -u -src sync.runtime_SemacquireRWMutex`):

```go
package sync // import "sync"

func runtime_SemacquireRWMutex(s *uint32, lifo bool, skipframes int)
```

#### `sync.runtime_SemacquireRWMutexR` (new)

Model (goose/model/overlay/sync/runtime.go:55):

```go
// MODEL: as runtime_Semacquire: lifo and skipframes only order the waiters
// and select the profiled stack frames.
func runtime_SemacquireRWMutexR(s *uint32, lifo bool, skipframes int) {
	runtime_Semacquire(s)
}
```

Real (`go doc -u -src sync.runtime_SemacquireRWMutexR`):

```go
package sync // import "sync"

// Semacquire(RW)Mutex(R) is like Semacquire, but for profiling contended
// Mutexes and RWMutexes.
// If lifo is true, queue waiter at the head of wait queue.
// skipframes is the number of frames to omit during tracing, counting from
// runtime_SemacquireMutex's caller.
// The different forms of this function just tell the runtime how to present
// the reason for waiting in a backtrace, and is used to compute some metrics.
// Otherwise they're functionally identical.
func runtime_SemacquireRWMutexR(s *uint32, lifo bool, skipframes int)
```

#### `sync.runtime_SemacquireWaitGroup` (new)

Model (goose/model/overlay/sync/runtime.go:48):

```go
// MODEL: as runtime_Semacquire: Go's differs only in the reason it reports
// for a parked goroutine and in synctest's durable blocking, which the model
// does not observe.
func runtime_SemacquireWaitGroup(s *uint32, synctestDurable bool) {
	runtime_Semacquire(s)
}
```

Real (`go doc -u -src sync.runtime_SemacquireWaitGroup`):

```go
package sync // import "sync"

// SemacquireWaitGroup is like Semacquire, but for WaitGroup.Wait.
func runtime_SemacquireWaitGroup(s *uint32, synctestDurable bool)
```

#### `sync.runtime_Semrelease` (new)

Model (goose/model/overlay/sync/runtime.go:66):

```go
// MODEL: Go's runtime_Semrelease (semrelease1) atomically increments *s and
// wakes a waiter if there is one (handing it the count directly if handoff);
// the model's waiters spin, so it is the increment.
func runtime_Semrelease(s *uint32, handoff bool, skipframes int) {
	atomic.AddUint32(s, 1)
}
```

Real (`go doc -u -src sync.runtime_Semrelease`):

```go
package sync // import "sync"

// Semrelease atomically increments *s and notifies a waiting goroutine
// if one is blocked in Semacquire.
// It is intended as a simple wakeup primitive for use by the synchronization
// library and should not be used directly.
// If handoff is true, pass count directly to the first waiter.
// skipframes is the number of frames to omit during tracing, counting from
// runtime_Semrelease's caller.
func runtime_Semrelease(s *uint32, handoff bool, skipframes int)
```

#### `sync.runtime_notifyListAdd` (new)

Model (goose/model/overlay/sync/runtime.go:73):

```go
// MODEL: Go's runtime_notifyListAdd (runtime/sema.go, notifyListAdd) is
//
//	return l.wait.Add(1) - 1
//
// the next ticket of the list, taken atomically; the model is the same over
// sync/atomic (wait is the runtime's atomic.Uint32, a uint32 in sync's copy of
// the type).
func runtime_notifyListAdd(l *notifyList) uint32 {
	return atomic.AddUint32(&l.wait, 1) - 1
}
```

Real (`go doc -u -src sync.runtime_notifyListAdd`):

```go
package sync // import "sync"

// See runtime/sema.go for documentation.
func runtime_notifyListAdd(l *notifyList) uint32
```

#### `sync.runtime_notifyListCheck` (new)

Model (goose/model/overlay/sync/runtime.go:137):

```go
// MODEL: Go's runtime_notifyListCheck throws if size is not the runtime's
// size of notifyList; the type is the real one, so its size is the runtime's,
// and the check passes.
func runtime_notifyListCheck(size uintptr) {
}
```

Real (`go doc -u -src sync.runtime_notifyListCheck`):

```go
package sync // import "sync"

// Ensure that sync and runtime agree on size of notifyList.
func runtime_notifyListCheck(size uintptr)
```

#### `sync.runtime_notifyListNotifyAll` (new)

Model (goose/model/overlay/sync/runtime.go:104):

```go
// MODEL: Go's runtime_notifyListNotifyAll (notifyListNotifyAll) returns if
// l.wait == l.notify (no waiter), and otherwise, under the list's lock, sets
// l.notify to l.wait and readies every parked waiter. The model reads both and
// sets l.notify with a compare-and-swap, retried if l.notify changed in
// between: the store linearizes at the compare-and-swap, as Go's does under
// the lock (the lock only orders the notify calls, which the compare-and-swap
// also does). The waiters are readied by the new l.notify (see
// runtime_notifyListWait).
func runtime_notifyListNotifyAll(l *notifyList) {
	for {
		n := atomic.LoadUint32(&l.notify)
		w := atomic.LoadUint32(&l.wait)
		if n == w || atomic.CompareAndSwapUint32(&l.notify, n, w) {
			return
		}
	}
}
```

Real (`go doc -u -src sync.runtime_notifyListNotifyAll`):

```go
package sync // import "sync"

// See runtime/sema.go for documentation.
func runtime_notifyListNotifyAll(l *notifyList)
```

#### `sync.runtime_notifyListNotifyOne` (new)

Model (goose/model/overlay/sync/runtime.go:122):

```go
// MODEL: Go's runtime_notifyListNotifyOne (notifyListNotifyOne) returns if
// l.wait == l.notify (no waiter), and otherwise, under the list's lock,
// increments l.notify and readies the waiter holding the old value as its
// ticket, if it has parked yet (if not, its Wait sees the ticket notified and
// returns at once). The model is the same increment by compare-and-swap,
// retried if l.notify changed in between (as for NotifyAll).
func runtime_notifyListNotifyOne(l *notifyList) {
	for {
		n := atomic.LoadUint32(&l.notify)
		if n == atomic.LoadUint32(&l.wait) || atomic.CompareAndSwapUint32(&l.notify, n, n+1) {
			return
		}
	}
}
```

Real (`go doc -u -src sync.runtime_notifyListNotifyOne`):

```go
package sync // import "sync"

// See runtime/sema.go for documentation.
func runtime_notifyListNotifyOne(l *notifyList)
```

#### `sync.runtime_notifyListWait` (new)

Model (goose/model/overlay/sync/runtime.go:84):

```go
// MODEL: Go's runtime_notifyListWait (notifyListWait) returns at once if
// ticket t has been notified, less(t, l.notify) with
//
//	func less(a, b uint32) bool {
//		return int32(a-b) < 0
//	}
//
// and otherwise parks until a notify call readies it, which the notify calls
// do exactly when they advance l.notify past t (NotifyOne readies the waiter
// whose ticket is the old l.notify, NotifyAll every waiter). The model spins
// on the same test, reading l.notify atomically: it returns exactly when Go's
// can. A goroutine that is never notified spins forever where Go's parks
// forever: spinning for parking is partial correctness, and Go's deadlock
// detector (a global deadlock becomes the fatal throw "all goroutines are
// asleep") is not modelled (docs/KNOWN_LIMITATIONS.md).
func runtime_notifyListWait(l *notifyList, t uint32) {
	for int32(t-atomic.LoadUint32(&l.notify)) >= 0 {
	}
}
```

Real (`go doc -u -src sync.runtime_notifyListWait`):

```go
package sync // import "sync"

// See runtime/sema.go for documentation.
func runtime_notifyListWait(l *notifyList, t uint32)
```

#### `sync.runtime_registerPoolCleanup` (new)

Model (goose/model/overlay/sync/pool.go:101):

```go
// MODEL: Go's runtime_registerPoolCleanup (a runtime push linkname, no Go
// body) records poolCleanup for the GC to call at the start of each cycle;
// poolCleanup moves the per-P pools to the victim cache. The model has no GC,
// and its pools' state is not in the per-P pools, which only the replaced
// Get and Put used, so recording it changes nothing.
func runtime_registerPoolCleanup(cleanup func()) {
}
```

Real (`go doc -u -src sync.runtime_registerPoolCleanup`):

```go
package sync // import "sync"

// Implemented in runtime.
func runtime_registerPoolCleanup(cleanup func())
```

Additions (no claim of their own; a primitive stub carries the TrustedCode claim, R2; an added method must match `added_methods`):

- `poolModel` (type, goose/model/overlay/sync/pool.go:15, new)
- `poolModelOf` (func, goose/model/overlay/sync/pool.go:28, new)
- `poolModelAt` (func, goose/model/overlay/sync/pool.go:41, new); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)

### Perennial/Code/time.toml  (package `time`)

- `[model]` before: none
- `[model]` after:  dir = 'goose/model/overlay/time', replaces = ['runtimeNow', 'runtimeNano', 'runtimeIsBubbled', 'newTimer', 'stopTimer', 'resetTimer', 'NewTimer', 'After', 'NewTicker', 'Ticker.Stop', 'Ticker.Reset'], added_methods = []
- model files: goose/model/overlay/time/sleep.go, goose/model/overlay/time/tick.go, goose/model/overlay/time/time.go; changed: goose/model/overlay/time/sleep.go, goose/model/overlay/time/tick.go, goose/model/overlay/time/time.go

#### `time.After` (new)

Model (goose/model/overlay/time/sleep.go:86):

```go
// MODEL: Go's After(d) is NewTimer(d).C: a timer that is never stopped or
// reset, whose channel delivers one value once the runtime clock reaches
// when(d). The model is NewTimer's (makeTimerChan, a firing that sends
// blocking, sendTimes), over the model's runtime clock (runtimeClock), which
// the proofs can speak of: when(d) is computed (whenAt) from a reading of that
// clock, and the firing goroutine waits until the clock reaches it
// (runtimeClockWaitUntil). The model's claim on the clock: the readings of
// Go's runtime clock form a non-decreasing sequence of positive int64s
// (runtimeNano), and the model's clock has every such sequence; Go's timer
// fires only once the clock has reached when.
func After(d Duration) <-chan Time {
	c := makeTimerChan()
	w := whenAt(runtimeClockNow(), d)
	checkWhen(w, 0)
	go func() {
		runtimeClockWaitUntil(w)
		sendTimes(c, 0, 0)
	}()
	return c
}
```

Real (`go doc -u -src time.After`):

```go
package time // import "time"

// After waits for the duration to elapse and then sends the current time
// on the returned channel.
// It is equivalent to [NewTimer](d).C.
//
// Before Go 1.23, this documentation warned that the underlying
// [Timer] would not be recovered by the garbage collector until the
// timer fired, and that if efficiency was a concern, code should use
// NewTimer instead and call [Timer.Stop] if the timer is no longer needed.
// As of Go 1.23, the garbage collector can recover unreferenced,
// unstopped timers. There is no reason to prefer NewTimer when After will do.
func After(d Duration) <-chan Time {
	return NewTimer(d).C
}
```

#### `time.NewTicker` (new)

Model (goose/model/overlay/time/tick.go:12):

```go
// MODEL: Go's NewTicker is
//
//	if d <= 0 {
//		panic("non-positive interval for NewTicker")
//	}
//	c := make(chan Time, 1)
//	t := (*Ticker)(unsafe.Pointer(newTimer(when(d), int64(d), sendTime, c, syncTimer(c))))
//	t.C = c
//	return t
//
// The model keeps the panic and is NewTimer's model otherwise (the channel,
// sendTimes), with the runtime's timer allocated as a Ticker
// (newRuntimeTicker) in place of the conversion, and armed with period d.
func NewTicker(d Duration) *Ticker {
	if d <= 0 {
		panic("non-positive interval for NewTicker")
	}
	c := makeTimerChan()
	w := when(d)
	fire := timerFunc(sendTimes, c)
	checkWhen(w, int64(d))
	t := newRuntimeTicker(fire)
	startTimer(fire, w, int64(d))
	t.C = c
	return t
}
```

Real (`go doc -u -src time.NewTicker`):

```go
package time // import "time"

// NewTicker returns a new [Ticker] containing a channel that will send
// the current time on the channel after each tick. The period of the
// ticks is specified by the duration argument. The ticker will adjust
// the time interval or drop ticks to make up for slow receivers.
// The duration d must be greater than zero; if not, NewTicker will
// panic.
//
// Before Go 1.23, the garbage collector did not recover
// tickers that had not yet expired or been stopped, so code often
// immediately deferred t.Stop after calling NewTicker, to make
// the ticker recoverable when it was no longer needed.
// As of Go 1.23, the garbage collector can recover unreferenced
// tickers, even if they haven't been stopped.
// The Stop method is no longer necessary to help the garbage collector.
// (Code may of course still want to call Stop to stop the ticker for other reasons.)
func NewTicker(d Duration) *Ticker {
	if d <= 0 {
		panic("non-positive interval for NewTicker")
	}
	// Give the channel a 1-element time buffer.
	// If the client falls behind while reading, we drop ticks
	// on the floor until the client catches up.
	c := make(chan Time, 1)
	t := (*Ticker)(unsafe.Pointer(newTimer(when(d), int64(d), sendTime, c, syncTimer(c))))
	t.C = c
	return t
}
```

#### `time.NewTimer` (new)

Model (goose/model/overlay/time/sleep.go:63):

```go
// MODEL: Go's NewTimer is
//
//	c := make(chan Time, 1)
//	t := newTimer(when(d), 0, sendTime, c, syncTimer(c))
//	t.C = c
//	return t
//
// syncTimer(c) is non-nil unless GODEBUG asynctimerchan=1, and then the
// runtime makes c synchronous: cap(c) and len(c) are 0, and a receive after a
// firing gets a value made at the receive. GooseLang cannot change a channel's
// kind after make, so the model makes c either way (makeTimerChan), and fires
// sendTimes in place of sendTime: sendTime's non-blocking send would drop the
// value on an unbuffered c, where the runtime delivers it at the next receive.
// sendTimes sends blocking, so a receive gets the value whenever it comes (or
// a later one: the model also allows values after Stop or Reset, which Go's
// synchronous channels never deliver).
func NewTimer(d Duration) *Timer {
	c := makeTimerChan()
	t := newTimer(when(d), 0, sendTimes, c, nil)
	t.C = c
	return t
}
```

Real (`go doc -u -src time.NewTimer`):

```go
package time // import "time"

// NewTimer creates a new Timer that will send
// the current time on its channel after at least duration d.
//
// Before Go 1.23, the garbage collector did not recover
// timers that had not yet expired or been stopped, so code often
// immediately deferred t.Stop after calling NewTimer, to make
// the timer recoverable when it was no longer needed.
// As of Go 1.23, the garbage collector can recover unreferenced
// timers, even if they haven't expired or been stopped.
// The Stop method is no longer necessary to help the garbage collector.
// (Code may of course still want to call Stop to stop the timer for other reasons.)
//
// Before Go 1.23, the channel associated with a Timer was
// asynchronous (buffered, capacity 1), which meant that
// stale time values could be received even after [Timer.Stop]
// or [Timer.Reset] returned.
// As of Go 1.23, the channel is synchronous (unbuffered, capacity 0),
// eliminating the possibility of those stale values.
//
// The GODEBUG setting asynctimerchan=1 restores both pre-Go 1.23
// behaviors: when set, unexpired timers won't be garbage collected, and
// channels will have buffered capacity. This setting may be removed
// in Go 1.27 or later.
func NewTimer(d Duration) *Timer {
	c := make(chan Time, 1)
	t := newTimer(when(d), 0, sendTime, c, syncTimer(c))
	t.C = c
	return t
}
```

#### `time.Ticker.Reset` (new)

Model (goose/model/overlay/time/tick.go:55):

```go
// MODEL: Go's Reset is
//
//	if d <= 0 {
//		panic("non-positive interval for Ticker.Reset")
//	}
//	if !t.initTicker {
//		panic("time: Reset called on uninitialized Ticker")
//	}
//	resetTimer((*Timer)(unsafe.Pointer(t)), when(d), int64(d))
//
// The model is the same with resetTimer's model at t's address
// (resetTimerAt) in place of the conversion.
func (t *Ticker) Reset(d Duration) {
	if d <= 0 {
		panic("non-positive interval for Ticker.Reset")
	}
	if !t.initTicker {
		panic("time: Reset called on uninitialized Ticker")
	}
	resetTimerAt(unsafe.Pointer(t), when(d), int64(d))
}
```

Real (`go doc -u -src time.Ticker.Reset`):

```go
package time // import "time"

// Reset stops a ticker and resets its period to the specified duration.
// The next tick will arrive after the new period elapses. The duration d
// must be greater than zero; if not, Reset will panic.
func (t *Ticker) Reset(d Duration) {
	if d <= 0 {
		panic("non-positive interval for Ticker.Reset")
	}
	if !t.initTicker {
		panic("time: Reset called on uninitialized Ticker")
	}
	resetTimer((*Timer)(unsafe.Pointer(t)), when(d), int64(d))
}
```

#### `time.Ticker.Stop` (new)

Model (goose/model/overlay/time/tick.go:39):

```go
// MODEL: Go's Stop is
//
//	if !t.initTicker {
//		return
//	}
//	stopTimer((*Timer)(unsafe.Pointer(t)))
//
// The model is the same with stopTimer's model at t's address (stopTimerAt)
// in place of the conversion, which is the identity on the address.
func (t *Ticker) Stop() {
	if !t.initTicker {
		return
	}
	stopTimerAt(unsafe.Pointer(t))
}
```

Real (`go doc -u -src time.Ticker.Stop`):

```go
package time // import "time"

// Stop turns off a ticker. After Stop, no more ticks will be sent.
// Stop does not close the channel, to prevent a concurrent goroutine
// reading from the channel from seeing an erroneous "tick".
func (t *Ticker) Stop() {
	if !t.initTicker {
		// This is misuse, and the same for time.Timer would panic,
		// but this didn't always panic, and we keep it not panicking
		// to avoid breaking old programs. See issue 21874.
		return
	}
	stopTimer((*Timer)(unsafe.Pointer(t)))
}
```

#### `time.newTimer` (new)

Model (goose/model/overlay/time/sleep.go:26):

```go
// MODEL: the runtime's newTimer (runtime/time.go) allocates a timer
// (runtime.timeTimer: the Timer's fields, then the runtime's state), sets
// initTimer, and arms it: once the runtime clock reaches when it calls
// f(arg, seq, delay) from the timer goroutine, and again every period if
// period != 0. The arming (timer.modify) throws if when <= 0 or period < 0;
// the model is stuck there (startTimer). Its channel argument cp only makes the
// timer's channel synchronous; NewTimer's and NewTicker's models pass nil and
// choose the channel's kind themselves (makeTimerChan), and AfterFunc passes
// nil. The model calls f with arbitrary seq and delay, so it covers the
// runtime's.
func newTimer(when, period int64, f func(any, uintptr, int64), arg any, cp unsafe.Pointer) *Timer {
	fire := timerFunc(f, arg)
	checkWhen(when, period)
	t := newRuntimeTimer(fire)
	startTimer(fire, when, period)
	return t
}
```

Real (`go doc -u -src time.newTimer`):

```go
package time // import "time"

// NewTimer creates a new Timer that will send
// the current time on its channel after at least duration d.
//
// Before Go 1.23, the garbage collector did not recover
// timers that had not yet expired or been stopped, so code often
// immediately deferred t.Stop after calling NewTimer, to make
// the timer recoverable when it was no longer needed.
// As of Go 1.23, the garbage collector can recover unreferenced
// timers, even if they haven't expired or been stopped.
// The Stop method is no longer necessary to help the garbage collector.
// (Code may of course still want to call Stop to stop the timer for other reasons.)
//
// Before Go 1.23, the channel associated with a Timer was
// asynchronous (buffered, capacity 1), which meant that
// stale time values could be received even after [Timer.Stop]
// or [Timer.Reset] returned.
// As of Go 1.23, the channel is synchronous (unbuffered, capacity 0),
// eliminating the possibility of those stale values.
//
// The GODEBUG setting asynctimerchan=1 restores both pre-Go 1.23
// behaviors: when set, unexpired timers won't be garbage collected, and
// channels will have buffered capacity. This setting may be removed
// in Go 1.27 or later.
func NewTimer(d Duration) *Timer {
	c := make(chan Time, 1)
	t := newTimer(when(d), 0, sendTime, c, syncTimer(c))
	t.C = c
	return t
}
// The arg cp is a chan Time, but the declaration in runtime uses a pointer,
// so we use a pointer here too. This keeps some tools that aggressively
// compare linknamed symbol definitions happier.
//
//go:linkname newTimer
func newTimer(when, period int64, f func(any, uintptr, int64), arg any, cp unsafe.Pointer) *Timer
```

#### `time.resetTimer` (new)

Model (goose/model/overlay/time/sleep.go:54):

```go
// MODEL: the runtime's resetTimer re-arms t (when, period: the arming throws
// as newTimer's does) and reports whether it was armed. The model loads t's
// runtime state as stopTimer does, is stuck where Go throws, starts one more
// firing goroutine with the state's call (startTimer) and returns an arbitrary
// bool. The earlier firings may still happen (as if Reset came later).
func resetTimer(t *Timer, when, period int64) bool {
	return resetTimerAt(unsafe.Pointer(t), when, period)
}
```

Real (`go doc -u -src time.resetTimer`):

```go
package time // import "time"

//go:linkname resetTimer
func resetTimer(t *Timer, when, period int64) bool
```

#### `time.runtimeIsBubbled` (new)

Model (goose/model/overlay/time/time.go:42):

```go
// MODEL: the runtime's runtimeIsBubbled is true exactly inside a
// testing/synctest bubble; the model has both results (gomodel.Choose).
func runtimeIsBubbled() bool {
	return gomodel.Choose()
}
```

Real (`go doc -u -src time.runtimeIsBubbled`):

```go
package time // import "time"

//go:linkname runtimeIsBubbled
func runtimeIsBubbled() bool
```

#### `time.runtimeNano` (new)

Model (goose/model/overlay/time/time.go:25):

```go
// MODEL: the runtime's runtimeNano (time_runtimeNano) is the bubble's fake
// clock inside a testing/synctest bubble, else nanotime(), the monotonic
// clock that now() also returns as mono. Both are positive: on Linux nanotime
// is CLOCK_MONOTONIC, the time since boot, and a bubble's clock starts at
// 2000-01-01 UTC; `when` relies on it ("runtimeNano() and d are always
// positive"), and the runtime's timers throw on a non-positive when. The model
// returns now()'s mono, with a non-positive one (which no Go run reads)
// replaced by 1, so that its readings are positive as Go's are and the
// models' timers can keep the runtime's throws (startTimer).
func runtimeNano() int64 {
	_, _, mono := now()
	if mono <= 0 {
		mono = 1
	}
	return mono
}
```

Real (`go doc -u -src time.runtimeNano`):

```go
package time // import "time"

// runtimeNano returns the current value of the runtime clock in nanoseconds.
// When called within a synctest.Run bubble, it returns the group's fake clock.
//
//go:linkname runtimeNano
func runtimeNano() int64
```

#### `time.runtimeNow` (new)

Model (goose/model/overlay/time/time.go:12):

```go
// MODEL: the runtime's runtimeNow (runtime/time.go, time_runtimeNow) is
//
//	if bubble := getg().bubble; bubble != nil {
//		return bubble.now / 1e9, int32(bubble.now % 1e9), 0
//	}
//	return time_now()
//
// and time_now is time.now's definition. The model returns now(), whose model
// is any (sec, nsec, mono); so it covers the bubble's fake clock too.
func runtimeNow() (sec int64, nsec int32, mono int64) {
	return now()
}
```

Real (`go doc -u -src time.runtimeNow`):

```go
package time // import "time"

// runtimeNow returns the current time.
// When called within a synctest.Run bubble, it returns the group's fake clock.
//
//go:linkname runtimeNow
func runtimeNow() (sec int64, nsec int32, mono int64)
```

#### `time.stopTimer` (new)

Model (goose/model/overlay/time/sleep.go:44):

```go
// MODEL: the runtime's stopTimer stops the runtime's timer t and reports
// whether it stopped it before it fired. The model loads t's runtime state
// (stuck if t is not one of the runtime's timers: a Timer the program
// allocated, or a copy, where Go reads memory that is not a timer) and returns
// an arbitrary bool; it does not stop the timer, whose firings may still
// happen (each one is a schedule of Go's in which Stop came later).
func stopTimer(t *Timer) bool {
	return stopTimerAt(unsafe.Pointer(t))
}
```

Real (`go doc -u -src time.stopTimer`):

```go
package time // import "time"

//go:linkname stopTimer
func stopTimer(*Timer) bool
```

Additions (no claim of their own; a primitive stub carries the TrustedCode claim, R2; an added method must match `added_methods`):

- `makeTimerChan` (func, goose/model/overlay/time/sleep.go:107, new)
- `sendTimes` (func, goose/model/overlay/time/sleep.go:128, new)
- `timerFunc` (func, goose/model/overlay/time/sleep.go:134, new)
- `checkWhen` (func, goose/model/overlay/time/sleep.go:142, new)
- `startTimer` (func, goose/model/overlay/time/sleep.go:150, new)
- `nextWhen` (func, goose/model/overlay/time/sleep.go:166, new)
- `sleepUntil` (func, goose/model/overlay/time/sleep.go:180, new)
- `stopTimerAt` (func, goose/model/overlay/time/sleep.go:191, new)
- `resetTimerAt` (func, goose/model/overlay/time/sleep.go:197, new)
- `newRuntimeTimer` (func, goose/model/overlay/time/sleep.go:205, new); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)
- `newRuntimeTicker` (func, goose/model/overlay/time/sleep.go:220, new); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)
- `runtimeTimerFire` (func, goose/model/overlay/time/sleep.go:231, new); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)
- `runtimeClock` (var, goose/model/overlay/time/sleep.go:242, new)
- `runtimeClockNow` (func, goose/model/overlay/time/sleep.go:246, new)
- `runtimeClockWaitUntil` (func, goose/model/overlay/time/sleep.go:259, new)
- `whenAt` (func, goose/model/overlay/time/sleep.go:270, new)

## Trusted models vs the Go source

### Perennial/TrustedCode/github_com/goose_lang/primitive.lean: `Assume.impl`

(the docstring quotes no Go code: the model must be read as GooseLang)

Real Go source (`go doc -src github.com/goose-lang/primitive.Assume`):

```go
package primitive // import "github.com/goose-lang/primitive"

// Assume lets the proof assume that `c` is true.
//
// In Go, if the assumption is violated this function will panic, whereas in the
// GooseLang model it will loop infinitely.
func Assume(c bool) {
	if !c {
		panic("Assume condition violated")
	}
}
```

### Perennial/TrustedCode/sync.lean: `poolModelAt.impl`

(the docstring quotes no Go code: the model must be read as GooseLang)

(`go doc -src sync.poolModelAt` found nothing: fetch the source yourself)

### Perennial/TrustedCode/time.lean: `now.impl`

(the docstring quotes no Go code: the model must be read as GooseLang)

Real Go source (`go doc -src time.now`):

```go
package time // import "time"

// Now returns the current local time.
func Now() Time {
	sec, nsec, mono := runtimeNow()
	if mono == 0 {
		return Time{uint64(nsec), sec + unixToInternal, Local}
	}
	mono -= startNano
	sec += unixToInternal - minWall
	if uint64(sec)>>33 != 0 {
		// Seconds field overflowed the 33 bits available when
		// storing a monotonic time. This will be true after
		// March 16, 2157.
		return Time{uint64(nsec), sec + minWall, Local}
	}
	return Time{hasMonotonic | uint64(sec)<<nsecShift | uint64(nsec), mono, Local}
}
```

### Perennial/TrustedCode/time.lean: `Sleep.impl`

(the docstring quotes no Go code: the model must be read as GooseLang)

Real Go source (`go doc -src time.Sleep`):

```go
package time // import "time"

// Sleep pauses the current goroutine for at least the duration d.
// A negative or zero duration causes Sleep to return immediately.
func Sleep(d Duration)
```

### Perennial/TrustedCode/time.lean: `newRuntimeTimer.impl`

(the docstring quotes no Go code: the model must be read as GooseLang)

(`go doc -src time.newRuntimeTimer` found nothing: fetch the source yourself)

### Perennial/TrustedCode/time.lean: `newRuntimeTicker.impl`

(the docstring quotes no Go code: the model must be read as GooseLang)

(`go doc -src time.newRuntimeTicker` found nothing: fetch the source yourself)

### Perennial/TrustedCode/time.lean: `runtimeTimerFire.impl`

(the docstring quotes no Go code: the model must be read as GooseLang)

(`go doc -src time.runtimeTimerFire` found nothing: fetch the source yourself)

