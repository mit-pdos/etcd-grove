/-
The pure vocabulary of net/url's escaping (Go 1.27.3, `url.go`, `encoding_table.go`), what its
translated functions compute:

* `shouldEscapeRef c mode`, `ishexRef c`: `gen_encoding_table.go`'s reference functions, from which Go
  generates the table `table` (`encoding_table.go`); `encTable c` the entry they give (bit `mode` set
  when `c` is not escaped in `mode`, bit 7 when `c` is a hex digit), `encTableList` the 256 entries.
  The package fact (`urlInit`, `Proof/net/url/PkgInit.lean`) says `table` holds them.
* `unhexF`, `unescapeF s mode` (`unescape`'s result: the decoded bytes, or the error it returns),
  `escapeF s mode` (`escape`), `validEncodedF s mode` (`validEncoded`), `escapedPathF rawPath path`
  (`URL.EscapedPath`).
-/
module

public import Perennial.Std.ByteString

@[expose] public section

noncomputable section

namespace Perennial

namespace net.url

/-! ### The encoding modes and the table -/

/-- `encodePath`, ..., `encodeFragment`, `hexChar`: the constants of `encoding_table.go`. -/
abbrev mPath : w8 := W8 1
abbrev mPathSegment : w8 := W8 2
abbrev mHost : w8 := W8 4
abbrev mZone : w8 := W8 8
abbrev mUserPassword : w8 := W8 16
abbrev mQueryComponent : w8 := W8 32
abbrev mFragment : w8 := W8 64
abbrev mHexChar : w8 := W8 128

/-- The seven encoding modes. -/
abbrev encModes : List w8 :=
  [mPath, mPathSegment, mHost, mZone, mUserPassword, mQueryComponent, mFragment]

/-- `lo ≤ c ≤ hi`, as bytes. -/
def inR (c : w8) (lo hi : Nat) : Bool := Nat.ble lo c.toNat && Nat.ble c.toNat hi

/-- `gen_encoding_table.go`'s `ishex`: `0-9`, `a-f`, `A-F`. -/
def ishexRef (c : w8) : Bool := inR c 48 57 || inR c 97 102 || inR c 65 70

/-- `gen_encoding_table.go`'s `shouldEscape(c, mode)` (RFC 3986's rules, as Go reads them), the
reference from which the table is generated. -/
def shouldEscapeRef (c : w8) (mode : w8) : Bool :=
  -- §2.3 unreserved (alphanum)
  if inR c 97 122 || inR c 65 90 || inR c 48 57 then false
  -- §3.2.2: `! $ & ' ( ) * + , ; = : [ ] < > "` in a host or zone
  else if (mode == mHost || mode == mZone) &&
      [W8 33, W8 36, W8 38, W8 39, W8 40, W8 41, W8 42, W8 43, W8 44, W8 59, W8 61, W8 58,
        W8 91, W8 93, W8 60, W8 62, W8 34].contains c then false
  -- §2.3 unreserved (mark): `- _ . ~`
  else if [W8 45, W8 95, W8 46, W8 126].contains c then false
  -- §2.2 reserved: `$ & + , / : ; = ? @`
  else if [W8 36, W8 38, W8 43, W8 44, W8 47, W8 58, W8 59, W8 61, W8 63, W8 64].contains c then
    if mode == mPath then c == W8 63
    else if mode == mPathSegment then c == W8 47 || c == W8 59 || c == W8 44 || c == W8 63
    else if mode == mUserPassword then c == W8 64 || c == W8 47 || c == W8 63 || c == W8 58
    else if mode == mQueryComponent then true
    else if mode == mFragment then false
    -- (host and zone: the reserved bytes not allowed above, none)
    else true
  -- the fragment's sub-delims `! ( ) *`
  else if mode == mFragment && [W8 33, W8 40, W8 41, W8 42].contains c then false
  else true

/-- The table's entry for `c`, as `gen_encoding_table.go`'s `generateTable` writes it: `hexChar` if
`c` is a hex digit, and each mode in which `c` is not escaped. -/
def encTable (c : w8) : w8 :=
  encModes.foldl (fun acc m => if shouldEscapeRef c m then acc else acc ||| m)
    (if ishexRef c then mHexChar else W8 0)

/-- The table's 256 entries. -/
def encTableList : List w8 := (List.range 256).map (fun n => encTable (BitVec.ofNat 8 n))

theorem encTableList_length : encTableList.length = 256 := by simp [encTableList]

theorem encTableList_get (c : w8) : encTableList[c.toNat]? = some (encTable c) := by
  simp [encTableList, c.isLt]

/-- The table checked against the reference, for every byte (by evaluation). -/
theorem encTable_check :
    (List.range 256).all (fun n => (encModes.all fun m =>
      (encTable (BitVec.ofNat 8 n) &&& m == W8 0) == shouldEscapeRef (BitVec.ofNat 8 n) m) &&
      ((encTable (BitVec.ofNat 8 n) &&& mHexChar != W8 0) == ishexRef (BitVec.ofNat 8 n))) = true := by
  set_option maxRecDepth 100000 in decide

theorem encTable_check_at (c : w8) :
    (encModes.all fun m => (encTable c &&& m == W8 0) == shouldEscapeRef c m) &&
      ((encTable c &&& mHexChar != W8 0) == ishexRef c) = true := by
  have h := List.all_eq_true.mp encTable_check c.toNat (List.mem_range.mpr c.isLt)
  simpa using h

/-- `shouldEscape(c, mode)` reads the table: `table[c]&mode == 0`; for a mode, that is the
reference's answer. -/
theorem encTable_mode (c : w8) (m : w8) (hm : m ∈ encModes) :
    (encTable c &&& m == W8 0) = shouldEscapeRef c m := by
  have h := encTable_check_at c
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.1 m hm

/-- `ishex(c)` reads the table: `table[c]&hexChar != 0`. -/
theorem encTable_hex (c : w8) : (encTable c &&& mHexChar != W8 0) = ishexRef c := by
  have h := encTable_check_at c
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact of_decide_eq_true h.2

/-! ### `unhex`, `unescape` -/

/-- `unhex(c)`: `9*(c>>6) + (c&15)`, the value of a hex digit. -/
def unhexF (c : w8) : w8 := W8 9 * c >>> W64 6 + (c &&& W8 15)

/-- The error `unescape` returns: `EscapeError(e)` or `InvalidHostError(e)`, `e` the offending bytes. -/
inductive UnescErr where
  | escape (e : List w8)
  | host (e : List w8)
  deriving DecidableEq

/-- `unescape`'s first loop, from the bytes `s` left: the first error, if any. -/
def unescCheck (mode : w8) : List w8 → Option UnescErr
  | [] => none
  | c :: rest =>
    if c == W8 37 then  -- '%'
      match rest with
      | a :: b :: rest' =>
        if !(ishexRef a && ishexRef b) then some (.escape (c :: a :: b :: []))
        else if mode == mHost && Nat.blt (unhexF a).toNat 8 && !(a == W8 50 && b == W8 53) then
          some (.escape [c, a, b])
        else if mode == mZone && !(a == W8 50 && b == W8 53) &&
            (unhexF a <<< W64 4 ||| unhexF b) != W8 32 &&
            shouldEscapeRef (unhexF a <<< W64 4 ||| unhexF b) mHost then
          some (.escape [c, a, b])
        else unescCheck mode rest'
      | _ => some (.escape (c :: rest))
    else if c == W8 43 then unescCheck mode rest  -- '+'
    else if (mode == mHost || mode == mZone) && Nat.blt c.toNat 128 && shouldEscapeRef c mode then
      some (.host [c])
    else unescCheck mode rest

/-- `unescape`'s second loop: each `%AB` decoded, `+` a space in a query component. -/
def unescDecode (mode : w8) : List w8 → List w8
  | [] => []
  | c :: rest =>
    if c == W8 37 then
      match rest with
      | a :: b :: rest' => (unhexF a <<< W64 4 ||| unhexF b) :: unescDecode mode rest'
      | _ => c :: rest  -- (excluded by the check)
    else if c == W8 43 then (if mode == mQueryComponent then W8 32 else W8 43) :: unescDecode mode rest
    else c :: unescDecode mode rest

/-- `unescape(s, mode)`'s result: the error of its check, or the decoded bytes (when `s` has no
`%`, and no `+` in a query component, Go returns `s` itself, which is its decoding). -/
def unescapeF (s : List w8) (mode : w8) : Except UnescErr (List w8) :=
  match unescCheck mode s with
  | some e => .error e
  | none => .ok (unescDecode mode s)

/-! ### `escape`, `validEncoded`, `EscapedPath` -/

/-- `upperhex[i]`. -/
def hexDigit (i : w8) : w8 := (go!"0123456789ABCDEF").getD i.toNat (W8 0)

/-- `escape(s, mode)`: each byte to escape as `%AB` (a space `+` in a query component). -/
def escapeF (s : List w8) (mode : w8) : List w8 :=
  s.flatMap fun c =>
    if c == W8 32 && mode == mQueryComponent then [W8 43]
    else if shouldEscapeRef c mode then [W8 37, hexDigit (c >>> W64 4), hexDigit (c &&& W8 15)]
    else [c]

/-- `validEncoded(s, mode)`: every byte a sub-delim, `:`, `@`, `[`, `]`, `%`, or one not escaped. -/
def validEncodedF (s : List w8) (mode : w8) : Bool :=
  s.all fun c =>
    [W8 33, W8 36, W8 38, W8 39, W8 40, W8 41, W8 42, W8 43, W8 44, W8 59, W8 61, W8 58, W8 64,
      W8 91, W8 93, W8 37].contains c || !shouldEscapeRef c mode

/-- `u.EscapedPath()` of a URL with `RawPath` `raw` and `Path` `path`: `raw` when it is a valid
encoding of `path`, else `"*"` for `"*"`, else `path` escaped. -/
def escapedPathF (raw path : List w8) : List w8 :=
  if !raw.isEmpty && validEncodedF raw mPath &&
      (match unescapeF raw mPath with | .ok p => p == path | .error _ => false) then raw
  else if path == [W8 42] then [W8 42]
  else escapeF path mPath

end net.url

end Perennial
