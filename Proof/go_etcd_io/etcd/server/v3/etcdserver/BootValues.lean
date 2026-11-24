/-
**What Go computes at a first start, as pure definitions** (claim #34, stage 3, 2026-11-23;
`notes/bootstrap-proof-plan.md` §7.2). `bootstrap`'s contract names the member's id, the peers, their
contexts and the directory as parameters; Go computes each from the configuration
(`server/etcdserver/api/membership/member.go`, `cluster.go`, `bootstrap.go` at the etcd pin
`edc800c6f`). These definitions are those values: `bootstrap.spec` is stated at them (at any other
values its post is false, the plan's §0), and the final stage substitutes them for the top-level
statements' quantified `id`/`ps`/`ctxs` (the owner's decision 1 on #34). Nothing here is trusted: each
is a definition, and which Go function computes it is proved in the stage named.

- `sha1`: FIPS 180-4's SHA-1, written out (stage 2 proves `crypto/sha1.Sum` equal to it).
- `memberID urls token`: `computeMemberID(peerURLs, token, nil)` (`member.go`): the first eight bytes,
  big-endian, of `sha1(join(sort(urls), "") ++ token)`.
- `members`: `NewClusterFromURLsMap`'s members, one per initial-cluster entry, sorted by id
  (`MemberIDs()`'s order, `bootstrapRaftFromCluster`'s peers).
- `cid`: `genID()`: the first eight bytes, big-endian, of `sha1` of the sorted ids' big-endian bytes.
- `memberJSON`: the bytes `json.Marshal(*Member)` writes for a member (`Member`'s tags: `id`, then the
  embedded `RaftAttributes` `peerURLs`, `isLearner,omitempty`, then `Attributes` `name,omitempty`,
  `clientURLs,omitempty`): since stage 4 (2026-11-25) the encoding/json model's bytes
  (`membership.memberJson`, #24 J2) at a non-nil peer-URL slice (`memberJSON_eq`).

A peer URL's string is `url.URL.String()` of it, which this repository specifies for a URL of only the
scheme `http` and a plain host (`http.urlRootPlain`: `http://` and the host); `bootURLsPlain` is that
precondition on the initial cluster, which `bootstrap.spec` takes.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Perennial.TrustedCode.crypto.fips140
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Json

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bootGo

/-! ### SHA-1 (FIPS 180-4, §5.1.1, §6.1) -/

/-- The four bytes at `i` of `l`, big-endian. -/
def be32At (l : List w8) (i : Nat) : w32 :=
  BitVec.ofNat 32 ((l.drop i).take 4 |>.foldl (fun acc b => acc * 256 + b.toNat) 0)

/-- The big-endian bytes of a 32-bit word. -/
def bytes32 (x : w32) : List w8 :=
  [BitVec.ofNat 8 (x.toNat / 2 ^ 24), BitVec.ofNat 8 (x.toNat / 2 ^ 16),
    BitVec.ofNat 8 (x.toNat / 2 ^ 8), BitVec.ofNat 8 x.toNat]

/-- The big-endian bytes of a 64-bit word (`binary.BigEndian.PutUint64`). -/
def bytes64 (x : w64) : List w8 :=
  (List.range 8).map (fun i => BitVec.ofNat 8 (x.toNat / 2 ^ (8 * (7 - i))))

/-- The word of the first eight bytes, big-endian (`binary.BigEndian.Uint64(b[:8])`). -/
def be64 (l : List w8) : w64 :=
  BitVec.ofNat 64 ((l.take 8).foldl (fun acc b => acc * 256 + b.toNat) 0)

/-- The message padded (§5.1.1): a `1` bit, zeros to `56 mod 64` bytes, the bit length. -/
def pad (m : List w8) : List w8 :=
  m ++ [BitVec.ofNat 8 0x80] ++ List.replicate ((119 - m.length % 64) % 64) (BitVec.ofNat 8 0) ++
    bytes64 (BitVec.ofNat 64 (m.length * 8))

/-- The message schedule of a 64-byte block (§6.1.2 step 1). -/
def schedule (blk : List w8) : Array w32 := Id.run do
  let mut w : Array w32 := #[]
  for t in [0:16] do
    w := w.push (be32At blk (4 * t))
  for t in [16:80] do
    w := w.push ((w[t - 3]! ^^^ w[t - 8]! ^^^ w[t - 14]! ^^^ w[t - 16]!).rotateLeft 1)
  return w

/-- The state: five words. -/
abbrev St := w32 × w32 × w32 × w32 × w32

/-- One round `t` (§6.1.2 step 3). -/
def round (w : Array w32) (s : St) (t : Nat) : St :=
  let (a, b, c, d, e) := s
  let (f, k) : w32 × w32 :=
    if t < 20 then ((b &&& c) ||| (~~~b &&& d), BitVec.ofNat 32 0x5A827999)
    else if t < 40 then (b ^^^ c ^^^ d, BitVec.ofNat 32 0x6ED9EBA1)
    else if t < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), BitVec.ofNat 32 0x8F1BBCDC)
    else (b ^^^ c ^^^ d, BitVec.ofNat 32 0xCA62C1D6)
  (a.rotateLeft 5 + f + e + k + w[t]!, a, b.rotateLeft 30, c, d)

/-- One block's compression (§6.1.2). -/
def compress (h : St) (blk : List w8) : St :=
  let w := schedule blk
  let (a, b, c, d, e) := (List.range 80).foldl (round w) h
  let (h0, h1, h2, h3, h4) := h
  (h0 + a, h1 + b, h2 + c, h3 + d, h4 + e)

/-- The initial state (§5.3.1). -/
def init : St :=
  (BitVec.ofNat 32 0x67452301, BitVec.ofNat 32 0xEFCDAB89, BitVec.ofNat 32 0x98BADCFE,
    BitVec.ofNat 32 0x10325476, BitVec.ofNat 32 0xC3D2E1F0)

/-- **SHA-1 of `m`**: its 20-byte digest (`crypto/sha1.Sum`). -/
def sha1 (m : List w8) : List w8 :=
  let p := pad m
  let (h0, h1, h2, h3, h4) :=
    (List.range (p.length / 64)).foldl (fun h i => compress h ((p.drop (64 * i)).take 64)) init
  bytes32 h0 ++ bytes32 h1 ++ bytes32 h2 ++ bytes32 h3 ++ bytes32 h4

/-! ### The members -/

/-- Go's string order (bytewise, `sort.Strings`). -/
def strLe : GoString → GoString → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x.toNat < y.toNat then true else if y.toNat < x.toNat then false else strLe xs ys

/-- `url.URL.String()` of a plain URL (`http.urlRootPlain`): `http://` and the host. -/
def urlStr [GooseExts] (u : _root_.Perennial.net.url.URL) : GoString := go!"http://" ++ u.Host'

/-- **The initial cluster's URLs are plain** (`http.urlRootPlain`, each entry's): where `urlStr` is
`URL.String`. -/
def bootURLsPlain [GooseExts] (U : BootURLs) : Prop :=
  ∀ k, (U.initMap.lookup k).isSome → ∀ u ∈ U.initURLs k, http.urlRootPlain u

/-- **A member's id** (`computeMemberID(peerURLs, token, nil)`). -/
def memberID (urls : List GoString) (token : GoString) : w64 :=
  be64 (sha1 ((urls.mergeSort strLe).flatten ++ token))

/-- **The member of the initial cluster's entry `name`** (`NewMember(name, urls, token, nil)`): its
id, its peer URLs' strings, a voter, its name, no client URLs. -/
def memberOf [GooseExts] (U : BootURLs) (token name : GoString) : apply.MemberM :=
  let us := (U.initURLs name).map urlStr
  ⟨memberID us token, us, false, name, []⟩

/-- **The initial cluster's members, by id** (`NewClusterFromURLsMap`'s, in `MemberIDs()`' order). -/
noncomputable def members [GooseExts] (U : BootURLs) (token : GoString) : List apply.MemberM :=
  (U.initMap.domList.map (memberOf U token)).mergeSort (fun a b => decide (a.id.toNat ≤ b.id.toNat))

/-- **The peers** (`MemberIDs()`). -/
noncomputable def ps [GooseExts] (U : BootURLs) (token : GoString) : List w64 := (members U token).map (·.id)

/-- **The cluster's members map, by id** (`NewClusterFromURLsMap`'s `c.members[m.ID] = m`, each
member under its own id): what `membership.memAt`/`clusterMem` hold of a new cluster. -/
noncomputable def memMap [GooseExts] (U : BootURLs) (token : GoString) : GMap w64 apply.MemberM :=
  (members U token).foldl (fun mem m => mem.insert m.id m) ∅

/-- **This member's id** (`cfg.Name`'s entry: `MemberByName(cfg.Name).ID`). -/
def id [GooseExts] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) : w64 :=
  (memberOf U cfg.InitialClusterToken' cfg.Name').id

/-- **The initial cluster `bootstrapCluster` accepts** (pure; what a successful
`bootstrapNewClusterNoWAL` has checked, `bootstrap.go:379-414` at the pin): the configuration's own
name is an entry (`VerifyBootstrap`'s `hasLocalMember`, `config.go`: an error otherwise), so this
member's id is a peer; and the entries' ids are distinct and not `0` (`NewClusterFromURLsMap`,
`cluster.go`: "member exists with identical ID" and "cannot use 0 as member id" otherwise). A fact
of the configuration, which `bootstrapCluster.spec`'s success gives and the later callees take. -/
def membersOk [GooseExts] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) : Prop :=
  (U.initMap.lookup cfg.Name').isSome ∧ (ps U cfg.InitialClusterToken').Nodup ∧
    W64 0 ∉ ps U cfg.InitialClusterToken' ∧
    (memberOf U cfg.InitialClusterToken' cfg.Name').id ∈ ps U cfg.InitialClusterToken'

/-- **The initial cluster's ids distinct and not `0`, and not too many entries** (claim #34, stage 2,
2026-11-25: `NewClusterFromURLsMap`'s premises, `bootstrapCluster.spec`'s). The ids: if two entries
had one id, Go's `fmt.Errorf("member exists with identical ID %v", m)` formats the `*Member` by
reflection, which the model does not cover (a SHA-1 collision of two distinct URL sets, or one URL set
under two names, which `VerifyBootstrap`'s `CheckDuplicateURL` refuses); a fact of the configuration,
checked by evaluation (`memberID` is computable). None `0`: Go answers an id `0` with an error
(`cannot use 0 as member id`); excluded so that `NewClusterFromURLsMap`'s loop never returns (a fact
of the configuration too). The size: `genID`'s `make([]byte, 8*len(ids))` and
`sort.Sort` need it. The URLs' bytes (2026-11-25, after Perennial's real `strings.Join`, whose result must be
shorter than `2^61` bytes): each entry `k` and URL `u` count `k=http://host,`, fewer than `2^61` bytes in all,
which bounds both `URLsMap.String()`'s join (`VerifyBootstrap`) and each member's joined URLs
(`computeMemberID`); a decidable fact of the configuration, settled per example by evaluation. -/
def initMapOk [GooseExts] (U : BootURLs) (token : GoString) : Prop :=
  (U.initMap.domList.map (fun k => (memberOf U token k).id)).Nodup ∧
    W64 0 ∉ U.initMap.domList.map (fun k => (memberOf U token k).id) ∧ GMap.size U.initMap ≤ 2 ^ 58 ∧
    (U.initMap.domList.map (fun k => (U.initURLs k).length)).sum ≤ 2 ^ 62 ∧
    (U.initMap.domList.map (fun k => ((U.initURLs k).map (fun u => k.length + (urlStr u).length + 2)).sum)).sum <
      2 ^ 61

/-- **This member's id is not one of raft's local targets** (claim #34 stage 4, 2026-11-25; ledger,
"`bootstrapRaft.spec`: an id raft refuses"): raft v3.7's `Config.validate` refuses an id that
`IsLocalMsgTarget` names (`LocalAppendThread`, `math.MaxUint64`, and `LocalApplyThread`,
`math.MaxUint64 - 1`: `raft.go`, `StartNode` panics on the error), which `ConfigValid` (`rnStartCfg`, in
`bootOk`'s `Hraft`) excludes; etcd's `NewClusterFromURLsMap` checks only `0`. A pure fact of the
configuration's URLs and token (a SHA-1 of them), settled per example by evaluation. -/
def idRaftOk [GooseExts] (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs) : Prop :=
  id cfg U ≠ W64 18446744073709551615 ∧ id cfg U ≠ W64 18446744073709551614

/-- **Every initial-cluster entry has a peer URL** (claim #34 stage 4, 2026-11-25; ledger,
"`bootstrapRaftFromCluster`: a member with no peer URL"): then each member's peer-URL slice is not nil, and
`json.Marshal` writes its `peerURLs` as an array (`memberJSON`), which `bootstrapRaftFromCluster`'s proof needs
of the cluster's clone (`Member.specMem` keeps no slice's nil-ness). Go's `types.NewURLsMap` gives every
entry at least one URL; a pure fact of each example's configuration. -/
def urlsNe [GooseExts] (U : BootURLs) : Prop :=
  ∀ k, (U.initMap.lookup k).isSome → U.initURLs k ≠ []

/-- **The cluster's id** (`genID()`). -/
noncomputable def cid [GooseExts] (U : BootURLs) (token : GoString) : w64 :=
  be64 (sha1 ((ps U token).flatMap bytes64))

/-- **The directory**: each member's peer URLs' strings, `[]` for an id of no member. -/
noncomputable def dir [GooseExts] (U : BootURLs) (token : GoString) (i : w64) : List GoString :=
  match (members U token).find? (fun m => m.id = i) with
  | some m => m.peerURLs
  | none => []

/-! ### `json.Marshal(*Member)` -/

/-- **`json.Marshal` of a member** (claim #34 stage 4, 2026-11-25: the encoding/json model's bytes,
`membership.memberJson`, at a non-nil peer-URL slice; until then a hand-written FIPS-style rendering
`ascii "{\"id\":" ++ …`, cross-checked against Go, which no spec produced): `{"id":N,"peerURLs":[...]`,
then `"isLearner":true` if a learner, `"name":"..."` if named, `"clientURLs":[...]` if any, then `}`
(`memberJSON_eq`). The claim that these are real encoding/json's bytes is the model's (`models/json`,
`Proof/.../membership/Json.lean`). -/
def memberJSON [GooseExts] (m : apply.MemberM) : List w8 :=
  [W8 123] ++ go!"\"id\":" ++ models_lab.jsoncodec.decU64 m.id ++ go!",\"peerURLs\":" ++
    membership.jsonStrSlice false m.peerURLs ++
    (if m.isLearner then go!",\"isLearner\":true" else []) ++
    (if m.name = [] then [] else go!",\"name\":" ++ models_lab.jsoncodec.jsonQuote m.name) ++
    (if m.clientURLs = [] then [] else go!",\"clientURLs\":" ++
      membership.jsonStrSlice false m.clientURLs) ++ [W8 125]

/-- **The model's bytes of a member record are `memberJSON` of its value**, when its peer-URL slice is
not nil and its client-URL slice is not nil when it holds some. -/
theorem memberJSON_eq [GooseExts] (v : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Member)
    (ps cs : List GoString) (hp : v.RaftAttributes'.PeerURLs' ≠ slice.nil)
    (hc : cs ≠ [] → v.Attributes'.ClientURLs' ≠ slice.nil) :
    membership.memberJson v ps cs =
      memberJSON ⟨v.ID', ps, v.RaftAttributes'.IsLearner', v.Attributes'.Name', cs⟩ := by
  unfold membership.memberJson membership.memberFieldsJson memberJSON
  by_cases hcs : cs = []
  · subst hcs; simp [hp]
  · simp [hp, hc hcs, hcs]

/-- **The peers' contexts** (`bootstrapRaftFromCluster`'s `json.Marshal(cl.Member(id))`, in `ps`
order). -/
noncomputable def ctxs [GooseExts] (U : BootURLs) (token : GoString) : List (List w8) :=
  (members U token).map memberJSON

end bootGo
end EtcdGrove
end Perennial
