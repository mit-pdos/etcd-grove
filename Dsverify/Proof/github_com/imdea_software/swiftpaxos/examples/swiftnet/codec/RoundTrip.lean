/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/RoundTrip.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The parsers invert the encodings of `Spec/swift/Wire.lean` (the round trip of the codec, pure):
each parser on an encoding followed by any bytes returns the encoded value and those bytes.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Parse

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

open sp

section rt
variable [GooseExts]

theorem pU64_cU64 (x : w64) (r : List w8) : pU64 (cU64 x ++ r) = some (x, r) := by
  simp [pU64, cU64, u64Le_length, u64Le_to_word]

theorem pI32_cI32 (x : w32) (r : List w8) : pI32 (cI32 x ++ r) = some (x, r) := by
  simp only [pI32, cI32, pU64_cU64]
  have h1 : sint.Z (BitVec.signExtend 64 x) = sint.Z x := by
    exact BitVec.toInt_signExtend_of_le (by omega)
  rw [h1, ite_eq_left (by word)]
  congr
  simp

theorem pU8_cU64 (x : w8) (r : List w8) :
    pU8 (cU64 (BitVec.zeroExtend 64 x) ++ r) = some (x, r) := by
  simp only [pU8, pU64_cU64]
  rw [ite_eq_left (by word)]
  congr
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem pBool_cBool (b : Bool) (r : List w8) : pBool (cBool b ++ r) = some (b, r) := by
  cases b <;> simp [pBool, cBool] <;> decide

theorem pBytes_cBytes (s r : List w8) (h : s.length < 2 ^ 64) :
    pBytes (cBytes s ++ r) = some (s, r) := by
  simp only [pBytes, cBytes, List.append_assoc, pU64_cU64]
  have : uint.nat (W64 s.length) = s.length := by word
  rw [this]
  simp

theorem pRep_flatten {A B : Type} (p : List w8 → Option (A × List w8)) (f : B → List w8)
    (g : B → A) (l : List B) (hp : ∀ x ∈ l, ∀ r, p (f x ++ r) = some (g x, r)) (r : List w8) :
    pRep p l.length ((l.map f).flatten ++ r) = some (l.map g, r) := by
  induction l with
  | nil => simp [pRep]
  | cons x l ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, pRep,
      hp x (List.mem_cons_self ..), ih (fun y hy => hp y (List.mem_cons_of_mem _ hy))]

theorem length_flatten_ge {B : Type} (f : B → List w8) (hne : ∀ x, 1 ≤ (f x).length) (l : List B) :
    l.length ≤ (l.map f).flatten.length := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.length_cons, List.map_cons, List.flatten_cons, List.length_append]; have := hne x; omega

theorem pList_cList {A B : Type} (p : List w8 → Option (A × List w8)) (f : B → List w8)
    (g : B → A) (hne : ∀ x, 1 ≤ (f x).length)
    (l : List B) (hp : ∀ x ∈ l, ∀ r, p (f x ++ r) = some (g x, r)) (r : List w8)
    (hl : l.length < 2 ^ 64) :
    pList p (cList f l ++ r) = some (l.map g, r) := by
  have h1 := length_flatten_ge f hne l
  simp only [cList, List.append_assoc]
  simp only [pList]
  rw [pU64_cU64]
  have : uint.nat (W64 l.length) = l.length := by word
  dsimp only
  rw [this]
  rw [ite_eq_left (by rw [List.length_append]; omega), pRep_flatten p f g l hp]

theorem cList_length_ge {B : Type} (f : B → List w8) (hne : ∀ x, 1 ≤ (f x).length) (l : List B) :
    l.length ≤ (cList f l).length := by
  have := length_flatten_ge f hne l
  simp only [cList, cU64, List.length_append, u64Le_length]; omega

/-- The Go command id of a model command id. -/
def cmdIdGo (x : CmdId) : swift.CommandId := ⟨x.cl, x.seq⟩

theorem pCmdId_cCmdId (x : CmdId) (r : List w8) : pCmdId (cCmdId x ++ r) = some (cmdIdGo x, r) := by
  simp only [pCmdId, cCmdId, List.append_assoc, pI32_cI32, cmdIdGo]

theorem pCmd_cCmd (c : Cmd) (r : List w8) (h : c.val.length < 2 ^ 64) :
    pCmd (cCmd c ++ r) = some (c, r) := by
  simp only [pCmd, cCmd, List.append_assoc, pU8_cU64, pInt, pU64_cU64, pBytes_cBytes _ _ h]

theorem insertL_fresh {V : Type} (k : swift.CommandId) (v : V) (ps : List (swift.CommandId × V))
    (h : k ∉ ps.map Prod.fst) : map.insertL k v ps = ps ++ [(k, v)] := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [map.insertL, h.1, ih h.2]

theorem foldl_insertL_fresh {V : Type} (es acc : List (swift.CommandId × V))
    (h : ((acc ++ es).map Prod.fst).Nodup) :
    es.foldl (fun acc e => map.insertL e.1 e.2 acc) acc = acc ++ es := by
  induction es generalizing acc with
  | nil => simp
  | cons e es ih =>
    simp only [List.foldl_cons]
    have hfresh : e.1 ∉ acc.map Prod.fst := by
      intro hm
      simp only [List.map_append, List.map_cons] at h
      exact (List.nodup_append.1 h).2.2 _ hm _ (List.mem_cons_self ..) rfl
    rw [insertL_fresh _ _ _ hfresh, ih]
    · simp
    · simpa using h

theorem insertAll_nodup {V : Type} (es : List (swift.CommandId × V)) (h : (es.map Prod.fst).Nodup) :
    insertAll es = es := by
  unfold insertAll
  rw [foldl_insertL_fresh es [] (by simpa using h)]
  simp

theorem length_le_flatten {B : Type} (f : B → List w8) (l : List B) (x : B) (hx : x ∈ l) :
    (f x).length ≤ (l.map f).flatten.length := by
  induction l with
  | nil => cases hx
  | cons y l ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.1 hx with rfl | h
    · omega
    · have := ih h; omega

theorem pEntry_cat {V B : Type} (pv : List w8 → Option (V × List w8)) (fv : B → List w8)
    (gv : B → V) (k : CmdId) (x : B) (hv : ∀ r, pv (fv x ++ r) = some (gv x, r)) (r : List w8) :
    pEntry pv (cCmdId k ++ fv x ++ r) = some ((cmdIdGo k, gv x), r) := by
  simp only [pEntry, List.append_assoc, pCmdId_cCmdId, hv]

theorem cmdIdGo_inj : Function.Injective cmdIdGo := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [cmdIdGo, swift.CommandId.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h; rfl

theorem pMap_cList {V B : Type} (pv : List w8 → Option (V × List w8)) (fv : B → List w8)
    (gv : B → V) (l : List (CmdId × B)) (hnd : (l.map Prod.fst).Nodup)
    (hv : ∀ p ∈ l, ∀ r, pv (fv p.2 ++ r) = some (gv p.2, r)) (r : List w8)
    (hl : l.length < 2 ^ 64) :
    pMap pv (cList (fun p : CmdId × B => cCmdId p.1 ++ fv p.2) l ++ r) =
      some (l.map (fun p => (cmdIdGo p.1, gv p.2)), r) := by
  unfold pMap
  rw [pList_cList (pEntry pv) _ (fun p => (cmdIdGo p.1, gv p.2))
    (fun p => by simp [cCmdId, cI32, cU64, u64Le_length]; omega) l
    (fun p hp r => pEntry_cat pv fv gv p.1 p.2 (hv p hp) r) r hl]
  dsimp only
  rw [insertAll_nodup]
  simp only [List.map_map, Function.comp_def]
  rw [show (fun x : CmdId × B => cmdIdGo x.1) = cmdIdGo ∘ Prod.fst from rfl, ← List.map_map]
  exact List.nodup_map_of_injective cmdIdGo_inj hnd

theorem pOpt_cMapOpt {A B : Type} (pm : List w8 → Option (A × List w8)) (f : B → List w8)
    (h : List B → A) (o : Option (List B)) (r : List w8)
    (hm : ∀ l, o = some l → pm (cList f l ++ r) = some (h l, r)) :
    pOpt pm (cMapOpt f o ++ r) = some (o.map h, r) := by
  cases o with
  | none => simp [pOpt, cMapOpt]; word
  | some l => simp [pOpt, cMapOpt, hm l rfl]; word

theorem length_le_cList {B : Type} (f : B → List w8) (l : List B) (x : B) (hx : x ∈ l) :
    (f x).length ≤ (cList f l).length := by
  have := length_le_flatten f l x hx
  simp only [cList, List.length_append]; omega

theorem cList_le_cMapOpt {B : Type} (f : B → List w8) (l : List B) :
    (cList f l).length ≤ (cMapOpt f (some l)).length := by
  simp [cMapOpt]

/-- The Go contents of a decoded `MSync` holding the wire value `m` (Go command ids). -/
def goSync (m : SyncWire) : SyncVal :=
  ⟨m.rep, m.bal, m.phases.map (·.map (fun p => (cmdIdGo p.1, p.2))),
    m.cmds.map (·.map (fun p => (cmdIdGo p.1, p.2))),
    m.deps.map (·.map (fun p => (cmdIdGo p.1, p.2.map cmdIdGo)))⟩

/-- An `MSync`'s map listings have distinct keys (`KitVal.wf` of `Spec/swiftnet/Codec.lean`). -/
def syncWf (m : SyncWire) : Prop :=
  (m.phases.map (fun l => (l.map Prod.fst).Nodup)).getD True ∧
    (m.cmds.map (fun l => (l.map Prod.fst).Nodup)).getD True ∧
    (m.deps.map (fun l => (l.map Prod.fst).Nodup)).getD True

theorem pMSync_cEnc (m : SyncWire) (hwf : syncWf m) (r : List w8)
    (hlen : (m.cEnc ++ r).length < 2 ^ 64) :
    pMSync (m.cEnc ++ r) = some (goSync m, r) := by
  obtain ⟨hw1, hw2, hw3⟩ := hwf
  simp only [SyncWire.cEnc, List.length_append] at hlen
  simp only [pMSync, SyncWire.cEnc, List.append_assoc, pI32_cI32]
  have hne1 : ∀ p : CmdId × w64, 1 ≤ (cCmdId p.1 ++ cU64 p.2).length := by
    intro p; simp [cCmdId, cI32, cU64, u64Le_length]
  have hne2 : ∀ p : CmdId × Cmd, 1 ≤ (cCmdId p.1 ++ cCmd p.2).length := by
    intro p; simp [cCmdId, cI32, cU64, u64Le_length]; omega
  have hne3 : ∀ p : CmdId × List CmdId, 1 ≤ (cCmdId p.1 ++ cList cCmdId p.2).length := by
    intro p; simp [cCmdId, cI32, cU64, u64Le_length]; omega
  rw [pOpt_cMapOpt (pMap pInt) _ (fun l => l.map (fun p => (cmdIdGo p.1, p.2))) m.phases _ (by
    intro l hl
    rw [hl] at hw1 hlen
    simp only [Option.map_some, Option.getD_some] at hw1
    have := cList_length_ge _ hne1 l
    have := cList_le_cMapOpt (fun p : CmdId × w64 => cCmdId p.1 ++ cU64 p.2) l
    exact pMap_cList pInt cU64 id l hw1 (fun p _ r => pU64_cU64 p.2 r) _ (by omega))]
  dsimp only
  rw [pOpt_cMapOpt (pMap pCmd) _ (fun l => l.map (fun p => (cmdIdGo p.1, p.2))) m.cmds _ (by
    intro l hl
    rw [hl] at hw2 hlen
    simp only [Option.map_some, Option.getD_some] at hw2
    have := cList_length_ge _ hne2 l
    have := cList_le_cMapOpt (fun p : CmdId × Cmd => cCmdId p.1 ++ cCmd p.2) l
    refine pMap_cList pCmd cCmd id l hw2 (fun p hp r => pCmd_cCmd p.2 r ?_) _ (by omega)
    have h1 := length_le_cList (fun p : CmdId × Cmd => cCmdId p.1 ++ cCmd p.2) l p hp
    have h2 : p.2.val.length ≤ (cCmdId p.1 ++ cCmd p.2).length := by
      simp only [cCmd, cBytes, List.length_append]; omega
    omega)]
  dsimp only
  rw [pOpt_cMapOpt (pMap (pList pCmdId)) _ (fun l => l.map (fun p => (cmdIdGo p.1, p.2.map cmdIdGo)))
    m.deps _ (by
    intro l hl
    rw [hl] at hw3 hlen
    simp only [Option.map_some, Option.getD_some] at hw3
    have := cList_length_ge _ hne3 l
    have := cList_le_cMapOpt (fun p : CmdId × List CmdId => cCmdId p.1 ++ cList cCmdId p.2) l
    refine pMap_cList (pList pCmdId) (cList cCmdId) (fun d => d.map cmdIdGo) l hw3
      (fun p hp r => pList_cList pCmdId cCmdId cmdIdGo
        (fun x => by simp [cCmdId, cI32, cU64, u64Le_length]) p.2
        (fun x _ r => pCmdId_cCmdId x r) r ?_) _ (by omega)
    have h1 := length_le_cList (fun p : CmdId × List CmdId => cCmdId p.1 ++ cList cCmdId p.2) l p hp
    have h2 := cList_length_ge cCmdId (fun x => by simp [cCmdId, cI32, cU64, u64Le_length]) p.2
    have h3 : (cList cCmdId p.2).length ≤ (cCmdId p.1 ++ cList cCmdId p.2).length := by
      simp only [List.length_append]; omega
    omega)]
  dsimp only
  rfl

end rt

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
section rt2
variable [GooseExts]
open sp

/-- The encoding of a value after its tag. -/
def kitBody : KitVal → List w8
  | .registerArgs a p => cBytes a ++ cU64 p
  | .registerReply i ns r l => cU64 i ++ cList cBytes ns ++ cBool r ++ cBool l
  | .getLeaderArgs => []
  | .getLeaderReply i => cU64 i
  | .getReplicaListArgs => []
  | .getReplicaListReply rs al r => cList cBytes rs ++ cList cBool al ++ cBool r
  | .pingArgs a => cU64 (BitVec.zeroExtend 64 a)
  | .pingReply => []
  | .beTheLeaderArgs => []
  | .beTheLeaderReply l n => cI32 l ++ cI32 n
  | .msync m => m.cEnc

theorem encode_eq (y : KitVal) : y.encode = cU64 (W64 y.tag) ++ kitBody y := by
  cases y <;> rfl

theorem tag_lt (y : KitVal) : y.tag < 18 := by cases y <;> simp [KitVal.tag]

/-- What the tag read from an encoding is. -/
theorem pU64_encode (y : KitVal) (bs : List w8) (hb : bs = y.encode) :
    pU64 bs = some (W64 y.tag, kitBody y) := by
  rw [hb, encode_eq, pU64_cU64]

theorem pU64_encode_inv (y : KitVal) (bs : List w8) (hb : bs = y.encode) (tag : w64)
    (rest : List w8) (h : pU64 bs = some (tag, rest)) : tag = W64 y.tag ∧ rest = kitBody y := by
  rw [pU64_encode y bs hb] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem tag_ne_of_W64 (y : KitVal) (t : Nat) (ht : t < 18) (h : W64 y.tag = W64 t) : y.tag = t := by
  have := tag_lt y
  have h' := congrArg BitVec.toNat h
  simp at h'
  omega

end rt2
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
section rt3
variable [GooseExts]
open sp

theorem cBytes_ne (s : List w8) : 1 ≤ (cBytes s).length := by
  simp [cBytes, cU64, u64Le_length]; omega

theorem pU64_nil (x : w64) : pU64 (cU64 x) = some (x, []) := by
  have := pU64_cU64 x []; simpa using this
theorem pI32_nil (x : w32) : pI32 (cI32 x) = some (x, []) := by
  have := pI32_cI32 x []; simpa using this
theorem pU8_nil (x : w8) : pU8 (cU64 (BitVec.zeroExtend 64 x)) = some (x, []) := by
  have := pU8_cU64 x []; simpa using this
theorem pBool_nil (b : Bool) : pBool (cBool b) = some (b, []) := by
  have := pBool_cBool b []; simpa using this

theorem rt_registerArgs (y : KitVal) (ht : y.tag = 1) (hl : (kitBody y).length < 2 ^ 64) :
    pRegisterArgs (kitBody y) = some (y, []) := by
  cases y <;> simp [KitVal.tag] at ht
  rename_i a p
  simp only [kitBody, List.length_append] at hl
  have ha : a.length < 2 ^ 64 := by simp [cBytes] at hl; omega
  simp only [pRegisterArgs, kitBody]
  rw [pBytes_cBytes _ _ ha]
  simp only [pInt, pU64_nil]

theorem rt_registerReply (y : KitVal) (ht : y.tag = 2) (hl : (kitBody y).length < 2 ^ 64) :
    pRegisterReply (kitBody y) = some (y, []) := by
  cases y <;> simp [KitVal.tag] at ht
  rename_i i ns rd il
  simp only [kitBody, List.length_append] at hl
  have hns := cList_length_ge cBytes cBytes_ne ns
  simp only [pRegisterReply, kitBody, List.append_assoc, pInt, pU64_cU64]
  rw [pList_cList pBytes cBytes id cBytes_ne ns (fun x hx r => by
      have := length_le_cList cBytes ns x hx
      exact pBytes_cBytes x r (by simp [cBytes] at this; omega)) _ (by omega)]
  dsimp only
  rw [pBool_cBool]
  dsimp only
  rw [pBool_nil]
  simp

theorem rt_getLeaderReply (y : KitVal) (ht : y.tag = 4) :
    pGetLeaderReply (kitBody y) = some (y, []) := by
  cases y <;> simp [KitVal.tag] at ht
  simp only [pGetLeaderReply, kitBody, pInt, pU64_nil]

theorem rt_getReplicaListReply (y : KitVal) (ht : y.tag = 6) (hl : (kitBody y).length < 2 ^ 64) :
    pGetReplicaListReply (kitBody y) = some (y, []) := by
  cases y <;> simp [KitVal.tag] at ht
  rename_i rs al rd
  simp only [kitBody, List.length_append] at hl
  have hrs := cList_length_ge cBytes cBytes_ne rs
  have hal := cList_length_ge cBool (fun b => by simp [cBool]) al
  simp only [pGetReplicaListReply, kitBody, List.append_assoc]
  rw [pList_cList pBytes cBytes id cBytes_ne rs (fun x hx r => by
      have := length_le_cList cBytes rs x hx
      exact pBytes_cBytes x r (by simp [cBytes] at this; omega)) _ (by omega)]
  dsimp only
  rw [pList_cList pBool cBool id (fun b => by simp [cBool]) al (fun x _ r => pBool_cBool x r) _
    (by omega)]
  dsimp only
  rw [pBool_nil]
  simp

theorem rt_pingArgs (y : KitVal) (ht : y.tag = 7) : pPingArgs (kitBody y) = some (y, []) := by
  cases y <;> simp [KitVal.tag] at ht
  simp only [pPingArgs, kitBody, pU8_nil]

theorem rt_beTheLeaderReply (y : KitVal) (ht : y.tag = 10) :
    pBeTheLeaderReply (kitBody y) = some (y, []) := by
  cases y <;> simp [KitVal.tag] at ht
  simp only [pBeTheLeaderReply, kitBody, pI32_cI32, pI32_nil]

theorem rt_empty (c y : KitVal) (hc : kitBody c = []) (ht : y.tag = c.tag)
    (hu : ∀ z : KitVal, z.tag = c.tag → z = c) : pEmpty c (kitBody y) = some (y, []) := by
  have := hu y ht
  subst this
  simp [pEmpty, hc]

/-- The Go contents of a decoded `MSync` value (for an `MSync`). -/
def syncOf : KitVal → SyncVal
  | .msync m => goSync m
  | _ => ⟨0, 0, none, none, none⟩

theorem rt_msync (y : KitVal) (ht : y.tag = 17) (hwf : kitWf y) (hl : (kitBody y).length < 2 ^ 64) :
    pMSync (kitBody y) = some (syncOf y, []) := by
  cases y <;> simp [KitVal.tag] at ht
  rename_i m
  simp only [kitBody] at hl ⊢
  rw [← List.append_nil m.cEnc, pMSync_cEnc m hwf [] (by simpa using hl)]
  rfl

end rt3
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
section rt4
variable [GooseExts]
open sp

theorem kitBody_len (y : KitVal) (bs : List w8) (hb : bs = y.encode) (hbs : bs.length < 2 ^ 64) :
    (kitBody y).length < 2 ^ 64 := by
  rw [hb, encode_eq] at hbs; simp at hbs; omega

/-- A tag other than `t`: no value of tag `t` was encoded. -/
theorem notEnc_of_tag (bs rest : List w8) (tag : w64) (t : Nat)
    (H : pU64 bs = some (tag, rest)) (h : ¬ tag = W64 t) :
    ∀ y : KitVal, y.tag = t → kitWf y → bs ≠ y.encode := by
  intro y hy _ hb
  obtain ⟨h1, -⟩ := pU64_encode_inv y bs hb _ _ H
  exact h (by rw [h1, hy])

/-- Decoding as the type of tag `t` (parser `p`, `rt` its round trip): the parsed value is the
encoded one, and a failed or partial parse means no value of the type was encoded. -/
structure DecAsFacts {A : Type} (p : List w8 → Option (A × List w8)) (t : Nat)
    (conv : KitVal → A) (bs rest : List w8) : Prop where
  ok : ∀ x, p rest = some (x, []) → ∀ y : KitVal, y.tag = t → kitWf y → bs = y.encode → x = conv y
  none : p rest = none → ∀ y : KitVal, y.tag = t → kitWf y → bs ≠ y.encode
  part : ∀ x rest2, p rest = some (x, rest2) → rest2 ≠ [] →
    ∀ y : KitVal, y.tag = t → kitWf y → bs ≠ y.encode

theorem decAsFacts {A : Type} (p : List w8 → Option (A × List w8)) (t : Nat)
    (conv : KitVal → A)
    (rt : ∀ y : KitVal, y.tag = t → kitWf y → (kitBody y).length < 2 ^ 64 →
      p (kitBody y) = some (conv y, []))
    (bs rest : List w8) (H : pU64 bs = some (W64 t, rest)) (hbs : bs.length < 2 ^ 64) :
    DecAsFacts p t conv bs rest where
  ok x hx y hy hwf hb := by
    obtain ⟨-, h2⟩ := pU64_encode_inv y bs hb _ _ H
    subst h2
    rw [rt y hy hwf (kitBody_len y bs hb hbs)] at hx
    cases hx; rfl
  none hn y hy hwf hb := by
    obtain ⟨-, h2⟩ := pU64_encode_inv y bs hb _ _ H
    subst h2
    rw [rt y hy hwf (kitBody_len y bs hb hbs)] at hn
    cases hn
  part x rest2 hx hne y hy hwf hb := by
    obtain ⟨-, h2⟩ := pU64_encode_inv y bs hb _ _ H
    subst h2
    rw [rt y hy hwf (kitBody_len y bs hb hbs)] at hx
    cases hx; exact hne rfl

end rt4
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
section rt5
variable [GooseExts]
open sp

theorem tag_eq_iff (z c : KitVal) (hc : ∀ z : KitVal, z.tag = c.tag → z = c) : z.tag = c.tag → z = c :=
  hc z

theorem rtU_registerArgs : ∀ y : KitVal, y.tag = 1 → kitWf y → (kitBody y).length < 2 ^ 64 →
    pRegisterArgs (kitBody y) = some (id y, []) := fun y hy _ hl => rt_registerArgs y hy hl
theorem rtU_registerReply : ∀ y : KitVal, y.tag = 2 → kitWf y → (kitBody y).length < 2 ^ 64 →
    pRegisterReply (kitBody y) = some (id y, []) := fun y hy _ hl => rt_registerReply y hy hl
theorem rtU_getLeaderReply : ∀ y : KitVal, y.tag = 4 → kitWf y → (kitBody y).length < 2 ^ 64 →
    pGetLeaderReply (kitBody y) = some (id y, []) := fun y hy _ _ => rt_getLeaderReply y hy
theorem rtU_getReplicaListReply : ∀ y : KitVal, y.tag = 6 → kitWf y →
    (kitBody y).length < 2 ^ 64 → pGetReplicaListReply (kitBody y) = some (id y, []) :=
  fun y hy _ hl => rt_getReplicaListReply y hy hl
theorem rtU_pingArgs : ∀ y : KitVal, y.tag = 7 → kitWf y → (kitBody y).length < 2 ^ 64 →
    pPingArgs (kitBody y) = some (id y, []) := fun y hy _ _ => rt_pingArgs y hy
theorem rtU_beTheLeaderReply : ∀ y : KitVal, y.tag = 10 → kitWf y → (kitBody y).length < 2 ^ 64 →
    pBeTheLeaderReply (kitBody y) = some (id y, []) := fun y hy _ _ => rt_beTheLeaderReply y hy
theorem rtU_msync : ∀ y : KitVal, y.tag = 17 → kitWf y → (kitBody y).length < 2 ^ 64 →
    pMSync (kitBody y) = some (syncOf y, []) := fun y hy hwf hl => rt_msync y hy hwf hl

theorem rtU_empty (c : KitVal) (hc : kitBody c = []) (hu : ∀ z : KitVal, z.tag = c.tag → z = c) :
    ∀ y : KitVal, y.tag = c.tag → kitWf y → (kitBody y).length < 2 ^ 64 →
      pEmpty c (kitBody y) = some (id y, []) := fun y hy _ _ => rt_empty c y hc hy hu

theorem rtU_getLeaderArgs : ∀ y : KitVal, y.tag = 3 → kitWf y → (kitBody y).length < 2 ^ 64 →
    pEmpty .getLeaderArgs (kitBody y) = some (id y, []) :=
  rtU_empty .getLeaderArgs rfl (fun z h => by cases z <;> simp_all [KitVal.tag])
theorem rtU_getReplicaListArgs : ∀ y : KitVal, y.tag = 5 → kitWf y → (kitBody y).length < 2 ^ 64 →
    pEmpty .getReplicaListArgs (kitBody y) = some (id y, []) :=
  rtU_empty .getReplicaListArgs rfl (fun z h => by cases z <;> simp_all [KitVal.tag])
theorem rtU_pingReply : ∀ y : KitVal, y.tag = 8 → kitWf y → (kitBody y).length < 2 ^ 64 →
    pEmpty .pingReply (kitBody y) = some (id y, []) :=
  rtU_empty .pingReply rfl (fun z h => by cases z <;> simp_all [KitVal.tag])
theorem rtU_beTheLeaderArgs : ∀ y : KitVal, y.tag = 9 → kitWf y → (kitBody y).length < 2 ^ 64 →
    pEmpty .beTheLeaderArgs (kitBody y) = some (id y, []) :=
  rtU_empty .beTheLeaderArgs rfl (fun z h => by cases z <;> simp_all [KitVal.tag])

end rt5
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
theorem cList_map {A B : Type} (f : B → List w8) (g : A → B) (xs : List A) :
    sp.cList f (xs.map g) = sp.cList (fun x => f (g x)) xs := by
  simp [sp.cList, List.map_map, Function.comp_def]
end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
