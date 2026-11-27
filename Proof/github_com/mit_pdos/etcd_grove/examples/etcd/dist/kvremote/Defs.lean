/-
`kvremote`'s vocabulary (`examples/etcd/dist/kvremote`): the bytes its encoders append for each of
txnlin's types, every field in order in `enc`'s encodings (`cmpBytes`, `tOpBytes`, `vrBytes`,
`tResBytes`, `kvBytes`, `inputBytes`, `outputBytes`), and their injectivity: an encoding is read back
from its bytes whatever follows, when the bytes fit in a slice (`_append_inj`; a string's length is
encoded as a `uint64`, so only strings shorter than `2 ^ 64` are told apart). `inputBytes_inj` and
`outputBytes_inj` are what the codec's decoders need (`codecOk`'s `DecIn`/`DecOut`) and the latter
what `remote.Run.spec`'s `hinj` is.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open github_com.mit_pdos.etcd_grove.examples.etcd.dist.enc
open github_com.mit_pdos.etcd_grove.examples.lib.txnwork

section bytes
variable [GooseExts]

/-- `encCmp`'s bytes. -/
def cmpBytes (c : Cmp) : List w8 :=
  encU64 c.Kind' ++ encStr c.Key' ++ encStr c.Val' ++ encU64 c.Num'

/-- `encTOp`'s bytes. -/
def tOpBytes (o : TOp) : List w8 := encU64 o.Kind' ++ encStr o.Key' ++ encStr o.Val'

/-- `encVR`'s bytes. -/
def vrBytes (r : VR) : List w8 := encStr r.Val' ++ encU64 r.Mod' ++ encU64 r.Ver'

/-- `encTRes`'s bytes. -/
def tResBytes (r : TRes) : List w8 :=
  encU64 r.Kind' ++ encBool r.Found' ++ vrBytes r.R' ++ encU64 r.N'

/-- `encKV`'s bytes. -/
def kvBytes (kv : KV) : List w8 := encStr kv.Key' ++ vrBytes kv.R'

/-- **`EncInput`'s bytes**: every field, in order. -/
def inputBytes (x : Input) : List w8 :=
  encU64 x.Kind' ++ encStr x.Key' ++ encStr x.Val' ++ encU64 x.NCmps' ++ cmpBytes x.Cmp0' ++
    encU64 x.NThen' ++ tOpBytes x.Then0' ++ tOpBytes x.Then1' ++ tOpBytes x.Then2' ++
    encU64 x.NElse' ++ tOpBytes x.Else0'

/-- **`EncOutput`'s bytes**: every field, in order. -/
def outputBytes (o : Output) : List w8 :=
  encBool o.Err' ++ encU64 o.Rev' ++ encBool o.Found' ++ vrBytes o.R' ++ encU64 o.N' ++
    encBool o.Ok' ++ encU64 o.NRes' ++ tResBytes o.Res0' ++ tResBytes o.Res1' ++
    tResBytes o.Res2' ++ encU64 o.NKVs' ++ kvBytes o.KV0' ++ kvBytes o.KV1' ++ kvBytes o.KV2'

/-! ## Injectivity -/

/-- `encStr_append_inj`, its bounds from the bytes' length. -/
theorem encStr_append_inj' {s t : GoString} {r r' : List w8} (h : encStr s ++ r = encStr t ++ r')
    (hb : (encStr s ++ r).length < 2 ^ 64) : s = t ∧ r = r' := by
  have ht : (encStr t ++ r').length < 2 ^ 64 := h ▸ hb
  simp only [encStr, List.length_append] at hb ht
  exact encStr_append_inj h (by omega) (by omega)

theorem cmpBytes_append_inj {a b : Cmp} {r r' : List w8} (h : cmpBytes a ++ r = cmpBytes b ++ r')
    (hb : (cmpBytes a ++ r).length < 2 ^ 64) : a = b ∧ r = r' := by
  cases a; cases b; simp only [cmpBytes, List.append_assoc] at h hb
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := encStr_append_inj' h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := encStr_append_inj' h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  exact ⟨rfl, h⟩

theorem tOpBytes_append_inj {a b : TOp} {r r' : List w8} (h : tOpBytes a ++ r = tOpBytes b ++ r')
    (hb : (tOpBytes a ++ r).length < 2 ^ 64) : a = b ∧ r = r' := by
  cases a; cases b; simp only [tOpBytes, List.append_assoc] at h hb
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := encStr_append_inj' h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := encStr_append_inj' h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  exact ⟨rfl, h⟩

theorem vrBytes_append_inj {a b : VR} {r r' : List w8} (h : vrBytes a ++ r = vrBytes b ++ r')
    (hb : (vrBytes a ++ r).length < 2 ^ 64) : a = b ∧ r = r' := by
  cases a; cases b; simp only [vrBytes, List.append_assoc] at h hb
  have hn := encStr_append_inj' h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  exact ⟨rfl, h⟩

theorem tResBytes_append_inj {a b : TRes} {r r' : List w8}
    (h : tResBytes a ++ r = tResBytes b ++ r') (hb : (tResBytes a ++ r).length < 2 ^ 64) :
    a = b ∧ r = r' := by
  cases a; cases b; simp only [tResBytes, List.append_assoc] at h hb
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := encBool_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := vrBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  exact ⟨rfl, h⟩

theorem kvBytes_append_inj {a b : KV} {r r' : List w8} (h : kvBytes a ++ r = kvBytes b ++ r')
    (hb : (kvBytes a ++ r).length < 2 ^ 64) : a = b ∧ r = r' := by
  cases a; cases b; simp only [kvBytes, List.append_assoc] at h hb
  have hn := encStr_append_inj' h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := vrBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  exact ⟨rfl, h⟩

theorem inputBytes_append_inj {a b : Input} {r r' : List w8}
    (h : inputBytes a ++ r = inputBytes b ++ r') (hb : (inputBytes a ++ r).length < 2 ^ 64) :
    a = b ∧ r = r' := by
  cases a; cases b; simp only [inputBytes, List.append_assoc] at h hb
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := encStr_append_inj' h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := encStr_append_inj' h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := cmpBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := tOpBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := tOpBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := tOpBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := tOpBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  exact ⟨rfl, h⟩

theorem outputBytes_append_inj {a b : Output} {r r' : List w8}
    (h : outputBytes a ++ r = outputBytes b ++ r') (hb : (outputBytes a ++ r).length < 2 ^ 64) :
    a = b ∧ r = r' := by
  cases a; cases b; simp only [outputBytes, List.append_assoc] at h hb
  have hn := encBool_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := encBool_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := vrBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := encBool_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := tResBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := tResBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := tResBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := encU64_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn
  have hn := kvBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := kvBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  have hn := kvBytes_append_inj h
  clear h
  obtain ⟨rfl, h⟩ := hn (by simp only [List.length_append] at hb ⊢; omega)
  exact ⟨rfl, h⟩

/-- **An input's encoding is read back** (bytes that fit in a slice). -/
theorem inputBytes_inj {a b : Input} (h : inputBytes a = inputBytes b)
    (hb : (inputBytes a).length < 2 ^ 64) : a = b :=
  (inputBytes_append_inj (r := []) (r' := []) (by simpa using h) (by simpa using hb)).1

/-- **An output's encoding is read back** (bytes that fit in a slice). -/
theorem outputBytes_inj {a b : Output} (h : outputBytes a = outputBytes b)
    (hb : (outputBytes a).length < 2 ^ 64) : a = b :=
  (outputBytes_append_inj (r := []) (r' := []) (by simpa using h) (by simpa using hb)).1

end bytes

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
