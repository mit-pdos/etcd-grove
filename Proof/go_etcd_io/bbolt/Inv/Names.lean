/-
The ghost names and namespaces of a database and of its transactions (U0a of
`notes/bbolt-proof-plan.md`; design §3.1, §3.7, §3.13).

`BoltName.gs` holds the database's ghost names by position (`bnsOf` reads them, with defaults
past the end); `mkGs` builds the list `Open` returns. bbolt's invariants live under the client's
namespace `γ.ns`.

The `Inv/` modules do not import `Spec/go_etcd_io/bbolt/Api.lean`, which imports them to seal its
predicates: they take a name's two parts, the decoded names `B : BNs` (`bnsOf γ.gs`) and the
namespace `N` (`γ.ns`), in place of a `BoltName` (U0a deviation, `notes/bbolt-proof-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.Data
public import Perennial.Proof.ProofPrelude
public import Perennial.GooseLang.Countable

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris

/-- **The decoded ghost names of a database** (design §3.1; the shares are the design's):
- `st`: `ghostVar Data`, the committed data (½ client, ¼ `metaR`, ¼ `rwR`/the writer);
- `bq`: `ghostVar Unit` at `q`, `boltState`'s validity (client only);
- `cur`: `ghostVar CommitSt` (½ `metaR`, ¼ `pagesInv`, ¼ `rwR`/the writer);
- `fl`: `ghostVar FLPg` (½ `pagesInv`, ½ `rwR`/the writer);
- `rds`: `ghostMap Nat RdInfo`, the registered readers (auth `pagesInv`);
- `fltx`: `ghostMap Nat w64`, the readers' txids (auth `metaR`, fragments deposited);
- `mtok`: `ghostVar Unit`, `mmaplock`'s token (`Pm q` holds `q`);
- `map`: `ghostVar MapSt` (½ `rwR`/the writer, ¼ `Pm`, ¼ `pagesInv`);
- `out`: `ghostVar Bool`, the meta cells' lending (½ `pagesInv`, ½ `rwR`/the writer);
- `mlk`: `ghostVar Unit`, whole in `metaR`, deposited by a meta-cell borrower;
- `wv`: `ghostVar (Option View)`, the writer's borrowed view (½ `pagesInv`, ½ the writer);
- `txs`: `ghostMap Loc TxReg`, the transactions (auth `txsInv`);
- `dbl`: `ghostVar Loc`, discarded: the database's location;
- `cls`: `ghostVar Bool`, closed (½ `rwR`, ½ `metaR`);
- `t0`: `ghostVar Nat`, discarded: the opened file's txid (the receipts' base);
- `pool`: the reader pool's name (round 4, N5). -/
structure BNs where
  st : GName
  bq : GName
  cur : GName
  fl : GName
  rds : GName
  fltx : GName
  mtok : GName
  map : GName
  out : GName
  mlk : GName
  wv : GName
  txs : GName
  dbl : GName
  cls : GName
  t0 : GName
  pool : GName
  deriving Inhabited

/-- The names of a `BoltName`'s list `gs` (`γ.gs`), by position. -/
def bnsOf (gs : List GName) : BNs :=
  ⟨gs.getD 0 default, gs.getD 1 default, gs.getD 2 default, gs.getD 3 default,
   gs.getD 4 default, gs.getD 5 default, gs.getD 6 default, gs.getD 7 default,
   gs.getD 8 default, gs.getD 9 default, gs.getD 10 default, gs.getD 11 default,
   gs.getD 12 default, gs.getD 13 default, gs.getD 14 default, gs.getD 15 default⟩

/-- The list of names `Open` returns (`⟨mkGs B, N⟩` is the database's `BoltName`). -/
def mkGs (B : BNs) : List GName :=
  [B.st, B.bq, B.cur, B.fl, B.rds, B.fltx, B.mtok, B.map, B.out, B.mlk, B.wv, B.txs, B.dbl,
    B.cls, B.t0, B.pool]

theorem bnsOf_mkGs (B : BNs) : bnsOf (mkGs B) = B := rfl

/-! ## Namespaces (under the client's `N = γ.ns`) -/

/-- The page store's invariant (`pagesInv`). -/
def pagesN (N : Namespace) : Namespace := N .@ "pages"
/-- The transactions' invariant (`txsInv`). -/
def txsN (N : Namespace) : Namespace := N .@ "txs"
/-- The reader pool. -/
def poolN (N : Namespace) : Namespace := N .@ "pool"

/-! ## Transactions -/

/-- The ghost names of a transaction (§3.7, §3.13):
- `v`: `ghostVar` of its agreed view and private state, at `q`;
- `ex`: `ghostVar Unit` at `q`, the exclusive part checked out;
- `bk`: `ghostMap Loc (GoString × Nat)`, the writer's handles (auth fractional in `boltTx`);
- `rbk`: `ghostMap Loc RHandle`, the reader's handles (auth in `txsInv`);
- `nl`: `ghostMap Loc (Loc × Nat)`, the writer's node-location registry (persistent
  fragments, N3);
- `done`: `ghostVar Bool`, the transaction is closed (½ `txsInv`, ½ the exclusive part);
- `pg`: `ghostMap Nat Unit`, the writer's page tokens (`txShape`, `Inv/Shape.lean`). -/
structure TxNames where
  v : GName
  ex : GName
  bk : GName
  rbk : GName
  nl : GName
  done : GName
  pg : GName
  deriving Inhabited, DecidableEq

instance TxNames.countable : Pos.Countable TxNames :=
  countableOfLeftInverse (fun n => (n.v, n.ex, n.bk, n.rbk, n.nl, n.done, n.pg))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-- Where a read transaction's (`mmaplock`, `statlock`) reader-token pair comes from (round 4,
N5): lent by the pool for a `threadTok`, or the writer side's spare pair (`freepages`). -/
inductive PairSrc where
  | loan
  | spare
  deriving Inhabited, DecidableEq

instance PairSrc.countable : Pos.Countable PairSrc :=
  countableOfLeftInverse (fun s => match s with | .loan => true | .spare => false)
    (fun b => if b then .loan else .spare) (fun s => by cases s <;> rfl)

/-- A registered transaction: its database, names, kind and pair source (`spare` for
writers). -/
structure TxReg where
  db : Loc
  n : TxNames
  rw : Bool
  src : PairSrc
  deriving Inhabited

instance TxReg.countable : Pos.Countable TxReg :=
  countableOfLeftInverse (fun r => (r.db, r.n, r.rw, r.src))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

end bbolt
end EtcdGrove
end Perennial
