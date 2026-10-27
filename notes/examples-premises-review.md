# The examples' adequacy theorems on the server port: premises for review

**2026-10-27 · branch `server-port` · proposed, not merged** (the user decides the final form of
these trusted statements; nothing here goes to `lean` without that review).

The examples (`putget`, `putget3`, `watchkv`, `cachekv`, `linkvtxn`, `k8setcd3`, `linkv3p`;
`authkv` has no adequacy theorem, its `premises` were ported the same way) moved onto the ported
server (`SrvRaft`, raft's node API). The change, in the shape the server port proposed
(`notes/decisions.md`, "etcd's server on raft's node API"), is confined to three premises; every
other hypothesis of every adequacy theorem is unchanged. The `*_safe` restatements in each
`Results.lean` changed identically.

## The changed premises (one sentence each)

1. **The bootstrap facts** (`putget.BootFacts`, `putget3.BootFacts`, `linkv3p.BootFacts` =
   putget3's): the bootstrap log is now the node API's `Draft.BootLog ps ctxs boot` (one
   `ConfChangeAddNode` per peer, at term 1, the peer's context `ctxs[k]`, marshalled) plus `cc`:
   each entry is a conf change of id `0` that the server's `applyConfChange` takes (`ccBootOk`);
   it changed because the server's cluster allocation (`srvClusterBoot_alloc`) takes exactly these
   instead of raft's `srvBootLogOk (ccOk ids) ids bootLog` over raft's records and conf-change
   policy `ccOk` (deleted). The theorem therefore quantifies `ctxs : List (List w8)` and
   `boot : List Draft.LogEntry` in place of `bootLog : List EntryM`.
2. **`bootstrap`'s contract** (the first clause of each `premises`, `putget3.bootPremise`,
   `linkv3p.bootPremise`): it is assumed at every server raft names `γ : SrvRaft` of the cluster
   with the right peers (`γ.vs = ids`), static (`γ.dyn = false`) and the given boot log
   (`γ.boot = toEntries boot 0`), at the storage registry those names carry (`⟨γ.reg⟩`; the
   separate `∀ reg` folded into `γ`), with the peers' contexts `ctxs` a parameter of the contract;
   it changed because `NewServer.spec` is now stated over `SrvRaft` (raft's `RaftNames`, its
   `reCCOk`/`reNoSnap`/`reNoXfer` modes and `reBoot` are gone from the server), and `bootOk` no
   longer chooses the contexts existentially nor gives `bootMarshal`.
3. **`proto.Marshal`'s contract at the boot log** (`bootMarshal ids ctxs (toEntries boot 0)`, a new
   conjunct of each `premises`): `proto.Marshal` of the `k`-th peer's `ConfChange` returns the
   `k`-th bootstrap entry's bytes; it is not new as an assumption (until now it was part of
   `bootstrap`'s contract's postcondition, `bootOk`'s `Hmarshal`) but it moved to a premise of its
   own because the cluster's allocation (`srvClusterBoot_alloc`, `Draft.cluster_alloc`) needs it
   *before* any member's `bootstrap` runs.

Not a new premise: `cluster_alloc`'s `receiptBound GF + boot.length ≤ 2 ^ 61` (raft-api,
2026-10-27) is discharged inside each proof (`common.alloc1`/`alloc3`'s `Hrb2`) from `receiptBound GF ≤ 2 ^ 48`,
which each theorem already derives from its `n + 2 ≤ 2 ^ 31`, and the boot log's length (1 or 3,
from `BootLog`).

## A finding the port had to work around: the storage registry is per member

`SrvRaft.reg` (the `MemoryStorage` registry, the instance `srvStor γ` the node predicates are
stated at) is one name in the cluster-wide `SrvRaft`, but `NewServer.spec` takes the registry's
full authority `memStorRegAuth ∅` at `γ.reg` for each member (each member's `bootstrap` joins its
own registry). For a three-member cluster that is unsatisfiable with one `γ`. The port gives each
member the cluster's names with its own registry, `{γ with reg := regᵢ}` (`common.alloc3`, the
cluster's invariants do not read `reg`: `common.srvRaftLogInv_reg` &c. are `BI.entails_refl`), and
relaxes `v3rpc.memberOf` (`HistoryModel.lean`, a server-side definition, not a top-level premise)
to "the raft names are the history's but for the registry". The cleaner fix is server-side: take
the registry out of `SrvRaft` (back to the member's `RNNames`, a binder of `NewServer.spec`, as
before the port), which would also restore the old premise's separate `∀ reg`. Not done here.

## The theorems' statements (before: `4dbbeeeaca`, after: this branch)

### `putget_adequate` (`putget/Adequacy.lean`)

```diff
--- putget_adequate (before)
+++ putget_adequate (after)
@@ -7,3 +7,4 @@
     (Hcec : ∀ hG : HeapGS .hasLC putgetGF, ContextErrsClient (GF := putgetGF) (hG := heapAt hG lctx))
-    (id : w64) (bootLog : List EntryM) (Hbf : putget.BootFacts id bootLog)
+    (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry)
+    (Hbf : putget.BootFacts id ctxs boot)
     (Hck : ckptEffectsOk) (Haf : authRecordsFit)
@@ -14,3 +15,3 @@
     (Hprem : ∀ hG : HeapGS .hasLC putgetGF,
-      ⊢ putget.premises (GF := putgetGF) (hG := heapAt hG lctx) n id bootLog)
+      ⊢ putget.premises (GF := putgetGF) (hG := heapAt hG lctx) n id ctxs boot)
     (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
```

### `putget3_adequate` (`putget3/Adequacy.lean`)

```diff
--- putget3_adequate (before)
+++ putget3_adequate (after)
@@ -7,3 +7,4 @@
     (Hcec : ∀ hG : HeapGS .hasLC putget3GF, ContextErrsClient (GF := putget3GF) (hG := heapAt3 hG lctx))
-    (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (Hbf : putget3.BootFacts id₁ id₂ id₃ bootLog)
+    (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry)
+    (Hbf : putget3.BootFacts id₁ id₂ id₃ ctxs boot)
     (Hck : ckptEffectsOk) (Haf : authRecordsFit)
@@ -14,3 +15,3 @@
     (Hprem : ∀ hG : HeapGS .hasLC putget3GF,
-      ⊢ putget3.premises (GF := putget3GF) (hG := heapAt3 hG lctx) n id₁ id₂ id₃ bootLog)
+      ⊢ putget3.premises (GF := putget3GF) (hG := heapAt3 hG lctx) n id₁ id₂ id₃ ctxs boot)
     (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
```

### `watch_adequate` (`watchkv/Adequacy.lean`)

```diff
--- watch_adequate (before)
+++ watch_adequate (after)
@@ -9,3 +9,4 @@
     (Hcec : ∀ hG : HeapGS .hasLC putgetGF, ContextErrsClient (GF := putgetGF) (hG := heapAt hG lctx))
-    (id : w64) (bootLog : List EntryM) (Hbf : putget.BootFacts id bootLog)
+    (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry)
+    (Hbf : putget.BootFacts id ctxs boot)
     (Hck : ckptEffectsOk) (Haf : authRecordsFit)
@@ -19,3 +20,3 @@
     (Hprem : ∀ hG : HeapGS .hasLC putgetGF,
-      ⊢ watchkv.premises (GF := putgetGF) (hG := heapAt hG lctx) n id bootLog)
+      ⊢ watchkv.premises (GF := putgetGF) (hG := heapAt hG lctx) n id ctxs boot)
     (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
```

### `cache_adequate` (`cachekv/Adequacy.lean`)

```diff
--- cache_adequate (before)
+++ cache_adequate (after)
@@ -9,3 +9,4 @@
     (Hcec : ∀ hG : HeapGS .hasLC putgetGF, ContextErrsClient (GF := putgetGF) (hG := heapAt hG lctx))
-    (id : w64) (bootLog : List EntryM) (Hbf : putget.BootFacts id bootLog)
+    (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry)
+    (Hbf : putget.BootFacts id ctxs boot)
     (Hck : ckptEffectsOk) (Haf : authRecordsFit)
@@ -19,3 +20,3 @@
     (Hprem : ∀ hG : HeapGS .hasLC putgetGF,
-      ⊢ cachekv.premises (GF := putgetGF) (hG := heapAt hG lctx) n id bootLog)
+      ⊢ cachekv.premises (GF := putgetGF) (hG := heapAt hG lctx) n id ctxs boot)
     (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
```

### `linkvtxn_adequate` (`linkvtxn/Adequacy.lean`)

```diff
--- linkvtxn_adequate (before)
+++ linkvtxn_adequate (after)
@@ -7,3 +7,4 @@
     (Hcec : ∀ hG : HeapGS .hasLC linkvtxnGF, ContextErrsClient (GF := linkvtxnGF) (hG := linkvtxnHeapAt hG lctx))
-    (id : w64) (bootLog : List EntryM) (Hbf : putget.BootFacts id bootLog)
+    (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry)
+    (Hbf : putget.BootFacts id ctxs boot)
     (Hck : ckptEffectsOk) (Haf : authRecordsFit)
@@ -17,3 +18,3 @@
     (Hprem : ∀ hG : HeapGS .hasLC linkvtxnGF,
-      ⊢ linkvtxn.premises (GF := linkvtxnGF) (hG := linkvtxnHeapAt hG lctx) n id bootLog)
+      ⊢ linkvtxn.premises (GF := linkvtxnGF) (hG := linkvtxnHeapAt hG lctx) n id ctxs boot)
     (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
```

### `k8setcd3_adequate` (`k8setcd3/Adequacy.lean`)

```diff
--- k8setcd3_adequate (before)
+++ k8setcd3_adequate (after)
@@ -9,3 +9,4 @@
     (Hctx : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextReadErrs (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
-    (id : w64) (bootLog : List EntryM) (Hbf : putget.BootFacts id bootLog)
+    (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry)
+    (Hbf : putget.BootFacts id ctxs boot)
     (Hck : ckptEffectsOk) (Haf : authRecordsFit)
@@ -19,3 +20,3 @@
     (Hprem : ∀ hG : HeapGS .hasLC k8setcd3GF,
-      ⊢ k8setcd3.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) n id bootLog)
+      ⊢ k8setcd3.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) n id ctxs boot)
     (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
```

### `linkv3p_adequate` (`linkv3p/Adequacy.lean`)

```diff
--- linkv3p_adequate (before)
+++ linkv3p_adequate (after)
@@ -8,3 +8,4 @@
     (Hcec : ∀ hG : HeapGS .hasLC linkvGF, ContextErrsClient (GF := linkvGF) (hG := linkvHeapAt hG lctx))
-    (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (Hbf : linkv3p.BootFacts id₁ id₂ id₃ bootLog)
+    (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry)
+    (Hbf : linkv3p.BootFacts id₁ id₂ id₃ ctxs boot)
     (Hck : ckptEffectsOk) (Haf : authRecordsFit)
@@ -20,3 +21,3 @@
     (Hprem : ∀ hG : HeapGS .hasLC linkvGF,
-      ⊢ linkv3p.premises (GF := linkvGF) (hG := linkvHeapAt hG lctx) n id₁ id₂ id₃ bootLog)
+      ⊢ linkv3p.premises (GF := linkvGF) (hG := linkvHeapAt hG lctx) n id₁ id₂ id₃ ctxs boot)
     (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
```

### `linkv3p_watch_adequate` (`linkv3p/AdequacyWatch.lean`)

```diff
--- linkv3p_watch_adequate (before)
+++ linkv3p_watch_adequate (after)
@@ -11,3 +11,4 @@
       ContextErrsClient (GF := linkvGF) (hG := linkvHeapAt hG lctx))
-    (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (Hbf : linkv3p.BootFacts id₁ id₂ id₃ bootLog)
+    (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry)
+    (Hbf : linkv3p.BootFacts id₁ id₂ id₃ ctxs boot)
     (Hck : ckptEffectsOk) (Haf : authRecordsFit)
@@ -23,3 +24,3 @@
     (Hprem : ∀ hG : HeapGS .hasLC linkvGF,
-      ⊢ linkv3p.premises (GF := linkvGF) (hG := linkvHeapAt hG lctx) n id₁ id₂ id₃ bootLog)
+      ⊢ linkv3p.premises (GF := linkvGF) (hG := linkvHeapAt hG lctx) n id₁ id₂ id₃ ctxs boot)
     (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
```

## The definitions the statements unfold to

#### `ccOk` (`putget/Defs.lean`)

```diff
--- before
+++ after
@@ -1,2 +0,0 @@
-def ccOk (id : w64) : w32 → List w8 → Prop := fun ty d =>
-  ty = W32 1 ∧ isConfChangeEncoding d ∧ ccIdOf d = W64 0 ∧ ccBootOk (GMap.listToSet [id]) d
```

#### `BootFacts` (`putget/Defs.lean`)

```diff
--- before
+++ after
@@ -1,3 +1,5 @@
-structure BootFacts (id : w64) (bootLog : List EntryM) : Prop where
+structure BootFacts (id : w64) (ctxs : List (List w8)) (bl : List Draft.LogEntry) : Prop where
   idLow : uint.Z id % 2 ^ 16 ≠ 0
-  boot : srvBootLogOk (ccOk id) [id] bootLog
+  boot : Draft.BootLog [id] ctxs bl
+  cc : ∀ e ∈ Draft.LogEntry.toEntries bl 0,
+    ccIdOf e.Data' = W64 0 ∧ ccBootOk (GMap.listToSet [id]) e.Data'
```

#### `premises` (`putget/Defs.lean`)

```diff
--- before
+++ after
@@ -1,11 +1,16 @@
-def premises (N : Nat) (id : w64) (bootLog : List EntryM) : IProp GF :=
+def premises (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry) :
+    IProp GF :=
   iprop(
-    -- `bootstrap`'s contract (D13b), at every storage registry and raft names of the one-member
-    -- cluster, for `Main`'s configuration and URLs (D19r (B), (F))
-    (□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
-        (γ : RaftNames),
-      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧
-        γ.reCCOk = ccOk id ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true⌝ -∗
-      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N (putgetDir id)) ∗
+    -- `bootstrap`'s contract (D13b), at every server raft names of the one-member cluster (2026-10-27,
+    -- the server port: its peers `[id]`, static, the bootstrap log; at the storage registry they
+    -- name), for `Main`'s configuration and URLs (D19r (B), (F)), at the peers' contexts `ctxs`
+    (□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
+      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.vs = [id] ∧ γ.dyn = false ∧
+        γ.boot = Draft.LogEntry.toEntries boot 0⌝ -∗
+      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N (putgetDir id)) ∗
+    -- (2026-10-27, the server port) `proto.Marshal` of the peers' conf changes returns the bootstrap
+    -- entries' bytes (raft's `bootMarshal`, which `StartNode` takes; the cluster's allocation's
+    -- premise; until then `bootstrap`'s contract gave it)
+    bootMarshal [id] ctxs (Draft.LogEntry.toEntries boot 0) ∗
     -- the raft wrapper's trust-boundary contracts (`NodeStartSpec`'s)
     rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
```

#### `premises` (`watchkv/Defs.lean`)

```diff
--- before
+++ after
@@ -1,9 +1,10 @@
-def premises (N : Nat) (id : w64) (bootLog : List EntryM) : IProp GF :=
+def premises (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry) :
+    IProp GF :=
   iprop(
-    (□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
-        (γ : RaftNames),
-      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧
-        γ.reCCOk = putget.ccOk id ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true⌝ -∗
-      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N (wkDir id)) ∗
+    (□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
+      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.vs = [id] ∧ γ.dyn = false ∧
+        γ.boot = Draft.LogEntry.toEntries boot 0⌝ -∗
+      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N (wkDir id)) ∗
+    bootMarshal [id] ctxs (Draft.LogEntry.toEntries boot 0) ∗
     rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
     (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
```

#### `premises` (`cachekv/Defs.lean`)

```diff
--- before
+++ after
@@ -1,9 +1,10 @@
-def premises (N : Nat) (id : w64) (bootLog : List EntryM) : IProp GF :=
+def premises (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry) :
+    IProp GF :=
   iprop(
-    (□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
-        (γ : RaftNames),
-      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧
-        γ.reCCOk = putget.ccOk id ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true⌝ -∗
-      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N (ckDir id)) ∗
+    (□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
+      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.vs = [id] ∧ γ.dyn = false ∧
+        γ.boot = Draft.LogEntry.toEntries boot 0⌝ -∗
+      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N (ckDir id)) ∗
+    bootMarshal [id] ctxs (Draft.LogEntry.toEntries boot 0) ∗
     rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
     (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
```

#### `premises` (`linkvtxn/MainDefs.lean`)

```diff
--- before
+++ after
@@ -1,9 +1,10 @@
-def premises (N : Nat) (id : w64) (bootLog : List EntryM) : IProp GF :=
+def premises (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry) :
+    IProp GF :=
   iprop(
-    (□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
-        (γ : RaftNames),
-      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧
-        γ.reCCOk = putget.ccOk id ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true⌝ -∗
-      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N (linkvtxnDir id)) ∗
+    (□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
+      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.vs = [id] ∧ γ.dyn = false ∧
+        γ.boot = Draft.LogEntry.toEntries boot 0⌝ -∗
+      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N (linkvtxnDir id)) ∗
+    bootMarshal [id] ctxs (Draft.LogEntry.toEntries boot 0) ∗
     rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
     (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
```

#### `premises` (`k8setcd3/MainDefs.lean`)

```diff
--- before
+++ after
@@ -1,9 +1,10 @@
-def premises (N : Nat) (id : w64) (bootLog : List EntryM) : IProp GF :=
+def premises (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry) :
+    IProp GF :=
   iprop(
-    (□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
-        (γ : RaftNames),
-      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.reCfg = GMap.listToSet [id] ∧ γ.reDyn = none ∧
-        γ.reCCOk = putget.ccOk id ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true⌝ -∗
-      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N (k8setcd3Dir id)) ∗
+    (□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
+      ⌜cfgOk cfg ∧ urlsOk U ∧ γ.vs = [id] ∧ γ.dyn = false ∧
+        γ.boot = Draft.LogEntry.toEntries boot 0⌝ -∗
+      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N (k8setcd3Dir id)) ∗
+    bootMarshal [id] ctxs (Draft.LogEntry.toEntries boot 0) ∗
     rnLoggerZapOk ∗ rnSetLoggerOk ∗ rnTimeoutDetectorOk ∗ rnNewStorageOk ∗
     (□ ∀ E : RNEnv GF, ⌜E.T = iprop(True)⌝ -∗ rnTickerOk E) ∗
```

#### `ccOk` (`putget3/Defs.lean`)

```diff
--- before
+++ after
@@ -1,2 +0,0 @@
-def ccOk (ps : List w64) : w32 → List w8 → Prop := fun ty d =>
-  ty = W32 1 ∧ isConfChangeEncoding d ∧ ccIdOf d = W64 0 ∧ ccBootOk (GMap.listToSet ps) d
```

#### `BootFacts` (`putget3/Defs.lean`)

```diff
--- before
+++ after
@@ -1,4 +1,7 @@
-structure BootFacts (id₁ id₂ id₃ : w64) (bootLog : List EntryM) : Prop where
+structure BootFacts (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (bl : List Draft.LogEntry) :
+    Prop where
   idLow : ([id₁, id₂, id₃].map (fun id => uint.Z id % 2 ^ 16)).Nodup
   idLow0 : ∀ id ∈ [id₁, id₂, id₃], uint.Z id % 2 ^ 16 ≠ 0
-  boot : srvBootLogOk (ccOk [id₁, id₂, id₃]) [id₁, id₂, id₃] bootLog
+  boot : Draft.BootLog [id₁, id₂, id₃] ctxs bl
+  cc : ∀ e ∈ Draft.LogEntry.toEntries bl 0,
+    ccIdOf e.Data' = W64 0 ∧ ccBootOk (GMap.listToSet [id₁, id₂, id₃]) e.Data'
```

#### `bootPremise` (`putget3/Defs.lean`)

```diff
--- before
+++ after
@@ -1,8 +1,6 @@
-def bootPremise (N : Nat) (ps : List w64) (bootLog : List EntryM) (dir : w64 → List GoString)
-    (name peerAddr client : GoString) (id : w64) : IProp GF :=
-  iprop(□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
-        (γ : RaftNames),
-      ⌜cfgOk name cfg ∧ urlsOk peerAddr client U ∧ γ.reCfg = GMap.listToSet ps ∧
-        γ.reDyn = none ∧ γ.reCCOk = ccOk ps ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧
-        γ.reNoXfer = true⌝ -∗
-      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N dir)
+def bootPremise (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
+    (dir : w64 → List GoString) (name peerAddr client : GoString) (id : w64) : IProp GF :=
+  iprop(□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
+      ⌜cfgOk name cfg ∧ urlsOk peerAddr client U ∧ γ.vs = ps ∧ γ.dyn = false ∧
+        γ.boot = bootLog⌝ -∗
+      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N dir)
```

#### `premises` (`putget3/Defs.lean`)

```diff
--- before
+++ after
@@ -1,6 +1,11 @@
-def premises (N : Nat) (id₁ id₂ id₃ : w64) (bootLog : List EntryM) : IProp GF :=
+def premises (N : Nat) (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry) :
+    IProp GF :=
   iprop(
-    bootPremise N [id₁, id₂, id₃] bootLog (dir3 id₁ id₂ id₃) name₁ peerAddr₁ clientAddr₁ id₁ ∗
-    bootPremise N [id₁, id₂, id₃] bootLog (dir3 id₁ id₂ id₃) name₂ peerAddr₂ clientAddr₂ id₂ ∗
-    bootPremise N [id₁, id₂, id₃] bootLog (dir3 id₁ id₂ id₃) name₃ peerAddr₃ clientAddr₃ id₃ ∗
+    bootPremise N [id₁, id₂, id₃] (Draft.LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
+      name₁ peerAddr₁ clientAddr₁ id₁ ∗
+    bootPremise N [id₁, id₂, id₃] (Draft.LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
+      name₂ peerAddr₂ clientAddr₂ id₂ ∗
+    bootPremise N [id₁, id₂, id₃] (Draft.LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
+      name₃ peerAddr₃ clientAddr₃ id₃ ∗
+    bootMarshal [id₁, id₂, id₃] ctxs (Draft.LogEntry.toEntries boot 0) ∗
     commonPremises)
```

#### `BootFacts` (`linkv3p/Defs.lean`)

```diff
--- before
+++ after
@@ -1,2 +1,2 @@
-abbrev BootFacts (id₁ id₂ id₃ : w64) (bootLog : List EntryM) : Prop :=
-  putget3.BootFacts id₁ id₂ id₃ bootLog
+abbrev BootFacts (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (bl : List Draft.LogEntry) : Prop :=
+  putget3.BootFacts id₁ id₂ id₃ ctxs bl
```

#### `bootPremise` (`linkv3p/Defs.lean`)

```diff
--- before
+++ after
@@ -1,7 +1,6 @@
-def bootPremise (N : Nat) (ps : List w64) (bootLog : List EntryM) (dir : w64 → List GoString)
-    (name peerAddr client : GoString) (id : w64) : IProp GF :=
-  iprop(□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
-        (γ : RaftNames),
-      ⌜cfgOk name cfg ∧ urlsOk peerAddr client U ∧ γ.reCfg = GMap.listToSet ps ∧
-        γ.reDyn = none ∧ γ.reCCOk = putget3.ccOk ps ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true⌝ -∗
-      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N dir)
+def bootPremise (N : Nat) (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8))
+    (dir : w64 → List GoString) (name peerAddr client : GoString) (id : w64) : IProp GF :=
+  iprop(□ ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) (γ : SrvRaft),
+      ⌜cfgOk name cfg ∧ urlsOk peerAddr client U ∧ γ.vs = ps ∧ γ.dyn = false ∧
+        γ.boot = bootLog⌝ -∗
+      letI : MemStorReg GF := ⟨γ.reg⟩; bootstrapContract cfg U γ id ctxs N dir)
```

#### `premises` (`linkv3p/Defs.lean`)

```diff
--- before
+++ after
@@ -1,6 +1,11 @@
-def premises (N : Nat) (id₁ id₂ id₃ : w64) (bootLog : List EntryM) : IProp GF :=
+def premises (N : Nat) (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry) :
+    IProp GF :=
   iprop(
-    bootPremise N (ids id₁ id₂ id₃) bootLog (dir3 id₁ id₂ id₃) name₁ peerAddr₁ clientAddr₁ id₁ ∗
-    bootPremise N (ids id₁ id₂ id₃) bootLog (dir3 id₁ id₂ id₃) name₂ peerAddr₂ clientAddr₂ id₂ ∗
-    bootPremise N (ids id₁ id₂ id₃) bootLog (dir3 id₁ id₂ id₃) name₃ peerAddr₃ clientAddr₃ id₃ ∗
+    bootPremise N (ids id₁ id₂ id₃) (Draft.LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
+      name₁ peerAddr₁ clientAddr₁ id₁ ∗
+    bootPremise N (ids id₁ id₂ id₃) (Draft.LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
+      name₂ peerAddr₂ clientAddr₂ id₂ ∗
+    bootPremise N (ids id₁ id₂ id₃) (Draft.LogEntry.toEntries boot 0) ctxs (dir3 id₁ id₂ id₃)
+      name₃ peerAddr₃ clientAddr₃ id₃ ∗
+    bootMarshal (ids id₁ id₂ id₃) ctxs (Draft.LogEntry.toEntries boot 0) ∗
     putget3.commonPremises)
```
