// Package jsoncodec holds the JSON syntax a generated encoding/json codec (jsongen.py, in the
// repository that keeps this module) and a model of encoding/json share: the scanner that
// finds where a JSON value ends in a byte stream (what the model's Decoder uses to frame values,
// and Unmarshal to validate), and the helpers the generated encoders and decoders call.
//
// A model of encoding/json cannot import this package (a standard-library package cannot import a
// module's); it gets Scan through the program's registered codec (json.SetCodec).
//
// The scanner (Scan, Valid, ValueEnd) is all of JSON's syntax, as Go 1.27.3's encoding/json
// scans it: whitespace, numbers, literals, strings with escape sequences and any bytes from 0x20
// up (encoding/json accepts invalid UTF-8), nesting up to encoding/json's depth limit, and every
// syntax error. It never panics.
//
// The encoders and the decoding of strings cover "plain" strings: only the bytes 0x20..0x7e other
// than '"' and '\\' (no escape sequences, no non-ASCII bytes). Real encoding/json writes exactly
// those bytes for a string of such bytes that has no '<', '>' or '&' (it escapes those three for
// HTML). Where a string leaves the subset (encoding one that real encoding/json would escape;
// decoding one with an escape sequence or a non-ASCII byte, which real encoding/json would
// unescape or replace), these functions block forever: the model is then stricter than Go, never more
// permissive, and a proof must show such strings never reach them. A string that is only skipped
// (an unknown member's, or inside a value decoded raw) may be any string.
//
// The trusted claim: these functions are real encoding/json's (Go 1.27.3) within the subset;
// tested against real encoding/json by jsoncodec_test.go and by each generated codec's test
// (json_gen_test.go).
package jsoncodec

// Scan's results.
const (
	// Done: b starts with a complete JSON value (after whitespace), which ends at n.
	Done uint64 = 0
	// More: b is whitespace, or a proper prefix of a value: more bytes are needed.
	More uint64 = 1
	// Bad: b does not start with a JSON value (a syntax error).
	Bad uint64 = 2
)

// MaxDepth is the deepest nesting of arrays and objects (real encoding/json's limit: deeper
// is a syntax error).
const MaxDepth = 10000

// IsSpace reports whether c is JSON whitespace.
func IsSpace(c byte) bool {
	return c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

// SkipSpace returns the index of the first byte of b at or after i that is not whitespace (or
// len(b)).
func SkipSpace(b []byte, i uint64) uint64 {
	j := i
	for j < uint64(len(b)) && IsSpace(b[j]) {
		j++
	}
	return j
}

func isDigit(c byte) bool {
	return '0' <= c && c <= '9'
}

// plainByte reports whether c may appear in a plain string's contents.
func plainByte(c byte) bool {
	return 0x20 <= c && c <= 0x7e && c != '"' && c != '\\'
}

// isHex reports whether c is a hexadecimal digit.
func isHex(c byte) bool {
	return isDigit(c) || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')
}

// scanString scans the string whose opening quote is at b[i]: (Done, end after the closing
// quote), More, or Bad (a control byte, or an escape JSON does not have). Any other byte is
// accepted (real encoding/json accepts invalid UTF-8 in a string).
func scanString(b []byte, i uint64) (uint64, uint64) {
	j := i + 1
	for j < uint64(len(b)) {
		c := b[j]
		if c == '"' {
			return Done, j + 1
		}
		if c < 0x20 {
			return Bad, j
		}
		if c == '\\' {
			if j+1 >= uint64(len(b)) {
				return More, j
			}
			e := b[j+1]
			if e == 'u' {
				k := j + 2
				for k < j+6 {
					if k >= uint64(len(b)) {
						return More, k
					}
					if !isHex(b[k]) {
						return Bad, k
					}
					k++
				}
				j = k
				continue
			}
			if e == '"' || e == '\\' || e == '/' || e == 'b' || e == 'f' || e == 'n' || e == 'r' || e == 't' {
				j = j + 2
				continue
			}
			return Bad, j
		}
		j++
	}
	return More, j
}

// scanDigits returns the index after the digits of b starting at i.
func scanDigits(b []byte, i uint64) uint64 {
	j := i
	for j < uint64(len(b)) && isDigit(b[j]) {
		j++
	}
	return j
}

// scanNumber scans the number starting at b[i] ('-' or a digit). A number ends at the first
// byte that cannot continue it; at the end of b it is complete only if eof (else More), and a
// number cut short at the end of b is More, never Bad.
func scanNumber(b []byte, i uint64, eof bool) (uint64, uint64) {
	n := uint64(len(b))
	j := i
	if b[j] == '-' {
		j++
		if j == n {
			return More, j
		}
		if !isDigit(b[j]) {
			return Bad, j
		}
	}
	if b[j] == '0' {
		j++
	} else {
		j = scanDigits(b, j)
	}
	if j == n {
		if eof {
			return Done, j
		}
		return More, j
	}
	if b[j] == '.' {
		j++
		if j == n {
			return More, j
		}
		if !isDigit(b[j]) {
			return Bad, j
		}
		j = scanDigits(b, j)
		if j == n {
			if eof {
				return Done, j
			}
			return More, j
		}
	}
	if b[j] == 'e' || b[j] == 'E' {
		j++
		if j < n && (b[j] == '+' || b[j] == '-') {
			j++
		}
		if j == n {
			return More, j
		}
		if !isDigit(b[j]) {
			return Bad, j
		}
		j = scanDigits(b, j)
		if j == n {
			if eof {
				return Done, j
			}
			return More, j
		}
	}
	return Done, j
}

// scanLiteral scans the literal lit (true, false, null) expected at b[i].
func scanLiteral(b []byte, i uint64, lit string) (uint64, uint64) {
	j := uint64(0)
	for j < uint64(len(lit)) {
		if i+j == uint64(len(b)) {
			return More, i + j
		}
		if b[i+j] != lit[j] {
			return Bad, i + j
		}
		j++
	}
	return Done, i + j
}

// scanScalar scans the value starting at b[i], a byte that is not whitespace, when it is not an
// array or an object.
func scanScalar(b []byte, i uint64, eof bool) (uint64, uint64) {
	c := b[i]
	if c == '"' {
		return scanString(b, i)
	}
	if c == '-' || isDigit(c) {
		return scanNumber(b, i, eof)
	}
	if c == 't' {
		return scanLiteral(b, i, "true")
	}
	if c == 'f' {
		return scanLiteral(b, i, "false")
	}
	if c == 'n' {
		return scanLiteral(b, i, "null")
	}
	return Bad, i
}

// Scan finds the end of the JSON value at the start of b (leading whitespace allowed):
// (Done, n) if b[:n] is whitespace followed by one complete value (an array, object, string or
// literal ends at its last byte; a number at the first byte that cannot continue it, or at the
// end of b if eof); (More, _) if b is whitespace or a proper prefix of a value (more bytes are
// needed; at eof the caller treats this as an unexpected end); (Bad, _) on a syntax error. It
// does not look past the value's end. Nesting deeper than MaxDepth is a syntax error.
func Scan(b []byte, eof bool) (uint64, uint64) {
	n := uint64(len(b))
	// stack: the open containers, '[' or '{'
	var stack []byte
	i := SkipSpace(b, 0)
	if i == n {
		return More, i
	}
	// state 0: a value is expected; 1: after a value; 2: an object key is expected
	// (after '{' when empty is allowed, or after ','); 3: after a key, ':' is expected
	state := uint64(0)
	// emptyOK: '}' or ']' may close the container here (right after its opening)
	emptyOK := false
	for {
		i = SkipSpace(b, i)
		if i == n {
			return More, i
		}
		c := b[i]
		if state == 0 {
			if c == '[' || c == '{' {
				if uint64(len(stack)) >= MaxDepth {
					return Bad, i
				}
				stack = append(stack, c)
				i++
				emptyOK = true
				if c == '{' {
					state = 2
				}
				continue
			}
			if c == ']' && emptyOK && stack[len(stack)-1] == '[' {
				stack = stack[:len(stack)-1]
				i++
				emptyOK = false
				if len(stack) == 0 {
					return Done, i
				}
				state = 1
				continue
			}
			// a number inside a container is complete only when a byte follows it
			st, j := scanScalar(b, i, eof && len(stack) == 0)
			if st != Done {
				return st, j
			}
			i = j
			emptyOK = false
			if len(stack) == 0 {
				return Done, i
			}
			state = 1
			continue
		}
		if state == 1 {
			top := stack[len(stack)-1]
			if c == ',' {
				i++
				if top == '{' {
					state = 2
				} else {
					state = 0
				}
				continue
			}
			if (c == ']' && top == '[') || (c == '}' && top == '{') {
				stack = stack[:len(stack)-1]
				i++
				if len(stack) == 0 {
					return Done, i
				}
				continue
			}
			return Bad, i
		}
		if state == 2 {
			if c == '}' && emptyOK {
				stack = stack[:len(stack)-1]
				i++
				emptyOK = false
				if len(stack) == 0 {
					return Done, i
				}
				state = 1
				continue
			}
			if c != '"' {
				return Bad, i
			}
			st, j := scanString(b, i)
			if st != Done {
				return st, j
			}
			i = j
			emptyOK = false
			state = 3
			continue
		}
		// state 3
		if c != ':' {
			return Bad, i
		}
		i++
		state = 0
	}
}

// Valid reports whether b is one JSON value with optional whitespace around it (encoding/json's
// Valid).
func Valid(b []byte) bool {
	st, n := Scan(b, true)
	if st != Done {
		return false
	}
	return SkipSpace(b, n) == uint64(len(b))
}

// ValueEnd returns the end of the value that starts at b[i] (after whitespace), for b[i:]
// starting with a complete value (as in the codec's decoders, whose input is valid): Scan's end,
// relative to b. It panics if there is none.
func ValueEnd(b []byte, i uint64) uint64 {
	st, n := Scan(b[i:], true)
	if st != Done {
		panic("jsoncodec: no complete value")
	}
	return i + n
}

// Nesting returns the deepest nesting of arrays and objects in b, a valid JSON text (0 for a
// scalar): the generated encoders add it to the depth a raw value is written at, against
// MaxDepth, as real encoding/json's encoder counts its nesting across a RawMessage.
func Nesting(b []byte) uint64 {
	depth := uint64(0)
	max := uint64(0)
	inStr := false
	i := 0
	for i < len(b) {
		c := b[i]
		if inStr {
			if c == '\\' {
				i++
			} else if c == '"' {
				inStr = false
			}
		} else if c == '"' {
			inStr = true
		} else if c == '[' || c == '{' {
			depth++
			if depth > max {
				max = depth
			}
		} else if c == ']' || c == '}' {
			depth--
		}
		i++
	}
	return max
}

// ---------------------------------------------------------------------------------------------
// Encoding (the generated encoders' helpers)

// Error is the error the generated codec returns: a decoding error that real encoding/json
// reports (a JSON value of the wrong kind for its Go type, a number out of range, ...), or a
// MarshalJSON / UnmarshalJSON method's error, or invalid output of a MarshalJSON method. Only
// whether there is an error is modeled, not its message or type.
type Error struct {
	Msg string
}

func (e *Error) Error() string {
	return "json: " + e.Msg
}

// Where real encoding/json does something the model does not reproduce (a string outside the
// plain subset, a type the codec does not know), these functions (and the generated codec) block
// forever (`select {}`), never panic: a panic can be recovered (Go's recover, Perennial's
// with_defer_recover), so a value panic would add behaviors encoding/json does not have; being
// stuck only removes behaviors (models/README.md), and a proof of the program shows nothing
// about a run that gets there.

// AppendRaw appends s's bytes to b.
func AppendRaw(b []byte, s string) []byte {
	return append(b, s...)
}

// htmlByte: the bytes real encoding/json escapes in a string for HTML (<, >, &).
func htmlByte(c byte) bool {
	return c == '<' || c == '>' || c == '&'
}

// AppendString appends s as a JSON string, as real encoding/json does for a plain s (its bytes
// in 0x20..0x7e, other than '"', '\\', '<', '>' and '&': written as they are, in quotes). It
// blocks forever for any other s (real encoding/json would escape or replace bytes: outside the model).
func AppendString(b []byte, s string) []byte {
	i := 0
	for i < len(s) {
		if !plainByte(s[i]) || htmlByte(s[i]) {
			select {} // MODEL: not modelled (stuck): json model: a string outside the model's plain subset
		}
		i++
	}
	b1 := append(b, '"')
	b2 := append(b1, s...)
	return append(b2, '"')
}

// AppendUint appends x in decimal.
func AppendUint(b []byte, x uint64) []byte {
	var digits [20]byte
	n := 0
	y := x
	for {
		digits[19-n] = byte('0' + y%10)
		n++
		y = y / 10
		if y == 0 {
			break
		}
	}
	return append(b, digits[20-n:]...)
}

// AppendQuotedUint appends x in decimal in quotes (a field with the ",string" option).
func AppendQuotedUint(b []byte, x uint64) []byte {
	b1 := append(b, '"')
	b2 := AppendUint(b1, x)
	return append(b2, '"')
}

// AppendInt appends x in decimal, with a '-' if it is negative (strconv.AppendInt(b, x, 10)).
func AppendInt(b []byte, x int64) []byte {
	if x >= 0 {
		return AppendUint(b, uint64(x))
	}
	// the magnitude of x, also for the smallest int64
	m := uint64(-(x + 1)) + 1
	return AppendUint(append(b, '-'), m)
}

// AppendQuotedInt appends x in decimal in quotes (a field with the ",string" option).
func AppendQuotedInt(b []byte, x int64) []byte {
	b1 := append(b, '"')
	b2 := AppendInt(b1, x)
	return append(b2, '"')
}

// AppendBool appends true or false.
func AppendBool(b []byte, x bool) []byte {
	if x {
		return append(b, "true"...)
	}
	return append(b, "false"...)
}

// AppendCompact appends a MarshalJSON method's output raw as real encoding/json does: false
// (an error) if raw is not one valid JSON value; else raw without its whitespace outside strings.
// It blocks forever (not modelled) if a string in raw has '<', '>', '&' (real encoding/json would escape them), an escape
// sequence or a non-ASCII byte (outside the model).
func AppendCompact(b []byte, raw []byte) ([]byte, bool) {
	if !Valid(raw) {
		return b, false
	}
	out := b
	inStr := false
	i := 0
	for i < len(raw) {
		c := raw[i]
		if inStr {
			if htmlByte(c) || c == '\\' || c >= 0x80 {
				select {} // MODEL: not modelled (stuck): json model: '<', '>', '&', an escape or a non-ASCII byte in a MarshalJSON string (outside the model)
			}
			if c == '"' {
				inStr = false
			}
			out = append(out, c)
		} else if !IsSpace(c) {
			if c == '"' {
				inStr = true
			}
			out = append(out, c)
		}
		i++
	}
	return out, true
}

// ---------------------------------------------------------------------------------------------
// Decoding (the generated decoders' helpers). Their input b is valid JSON (the model's
// Unmarshal and Decode validate it with Scan first), and i is at a value or at whitespace before
// one. A string they decode (a member's key, a string value) must be plain (they block forever otherwise).

// At returns the index of the value at or after i (after whitespace) and its first byte.
func At(b []byte, i uint64) (uint64, byte) {
	j := SkipSpace(b, i)
	return j, b[j]
}

// Str returns the contents of the string whose opening quote is at b[i], and the index after
// its closing quote.
func Str(b []byte, i uint64) (string, uint64) {
	j := i + 1
	for b[j] != '"' {
		if b[j] == '\\' || b[j] >= 0x80 {
			select {} // MODEL: not modelled (stuck): json model: decoding a string with an escape or a non-ASCII byte (outside the model's plain subset)
		}
		j++
	}
	return string(b[i+1 : j]), j + 1
}

// Member reads an object member's key at or after i (after whitespace; b[i..] is `"key" :`):
// the key and the index after the ':'.
func Member(b []byte, i uint64) (string, uint64) {
	j := SkipSpace(b, i)
	k, e := Str(b, j)
	e2 := SkipSpace(b, e)
	return k, e2 + 1
}

// Next is called after an object member's or array element's value, at or before the next ','
// or the closing bracket: (true, the index after ',') if another follows, (false, the index
// after the bracket) otherwise.
func Next(b []byte, i uint64) (bool, uint64) {
	j := SkipSpace(b, i)
	return b[j] == ',', j + 1
}

// Empty reports whether the array or object whose opening bracket is at b[i] is empty, and the
// index after its closing bracket if so (else after the opening one).
func Empty(b []byte, i uint64) (bool, uint64) {
	j := SkipSpace(b, i+1)
	if b[j] == ']' || b[j] == '}' {
		return true, j + 1
	}
	return false, i + 1
}

// lower is c in lower case (ASCII).
func lower(c byte) byte {
	if 'A' <= c && c <= 'Z' {
		return c + ('a' - 'A')
	}
	return c
}

// FoldEq reports whether k and name are equal ignoring ASCII case: how real encoding/json
// matches an object key with a struct field's name when no field's name is exactly the key (k
// and name are plain, so no other case folding applies).
func FoldEq(k string, name string) bool {
	if len(k) != len(name) {
		return false
	}
	i := 0
	for i < len(k) {
		if lower(k[i]) != lower(name[i]) {
			return false
		}
		i++
	}
	return true
}

// Digits parses b[i:j] as a decimal unsigned integer of at most max: (x, true), or false if it
// is empty, has a byte other than a digit, or is above max (real encoding/json's
// strconv.ParseUint(s, 10, bits) and range check for an unsigned field).
func Digits(b []byte, i uint64, j uint64, max uint64) (uint64, bool) {
	if i >= j {
		return 0, false
	}
	x := uint64(0)
	k := i
	for k < j {
		c := b[k]
		if !isDigit(c) {
			return 0, false
		}
		d := uint64(c - '0')
		if x > (max-d)/10 {
			return 0, false
		}
		x = x*10 + d
		k++
	}
	return x, true
}

// A scalar decoder's status: Set (the value decoded; store it), Keep (null: the target is left
// unchanged, as real encoding/json leaves it), TypeErr (a value of the wrong kind or out of
// range: real encoding/json records an error, leaves the target unchanged, and goes on).
const (
	Set     uint64 = 0
	Keep    uint64 = 1
	TypeErr uint64 = 2
)

// Uint decodes the value at or after i into an unsigned integer of at most max (max >= 9): a
// number with no sign, fraction or exponent, in range. It returns the number, the status and the
// index after the value.
func Uint(b []byte, i uint64, max uint64) (uint64, uint64, uint64) {
	j, c := At(b, i)
	k := ValueEnd(b, j)
	if c == 'n' {
		return 0, Keep, k
	}
	if !isDigit(c) {
		return 0, TypeErr, k
	}
	x, ok := Digits(b, j, k, max)
	if !ok {
		return 0, TypeErr, k
	}
	return x, Set, k
}

// QuotedUint decodes the value at or after i into an unsigned integer field tagged ",string": a
// string of decimal digits (leading zeros allowed) in range; null and the string "null" leave
// the field unchanged.
func QuotedUint(b []byte, i uint64, max uint64) (uint64, uint64, uint64) {
	j, c := At(b, i)
	k := ValueEnd(b, j)
	if c == 'n' {
		return 0, Keep, k
	}
	if c != '"' {
		return 0, TypeErr, k
	}
	noEscape(b, j+1, k-1)
	if k-j == 6 && b[j+1] == 'n' && b[j+2] == 'u' && b[j+3] == 'l' && b[j+4] == 'l' {
		return 0, Keep, k
	}
	x, ok := Digits(b, j+1, k-1, max)
	if !ok {
		return 0, TypeErr, k
	}
	return x, Set, k
}

// noEscape blocks forever if b[i:j] (a string's contents) has an escape sequence: real encoding/json
// unescapes a ",string" field's string before parsing it (an escaped digit is a digit), which the
// model does not.
func noEscape(b []byte, i uint64, j uint64) {
	k := i
	for k < j {
		if b[k] == '\\' {
			select {} // MODEL: not modelled (stuck): json model: an escape sequence in a ",string" field's string (outside the model's plain subset)
		}
		k++
	}
}

// Int decodes the value at or after i into a signed integer in [-max-1, max] (max >= 9; max+1 a
// power of two): a number with no fraction or exponent, '-' allowed. It returns the number, the
// status and the index after the value.
func Int(b []byte, i uint64, max uint64) (int64, uint64, uint64) {
	j, c := At(b, i)
	k := ValueEnd(b, j)
	if c == 'n' {
		return 0, Keep, k
	}
	return signed(b, j, k, max, false), statusOf(b, j, k, max, false), k
}

// QuotedInt decodes the value at or after i into a signed integer field tagged ",string": a
// string holding an optional sign ('+' or '-') and decimal digits (leading zeros allowed), in
// range (strconv.ParseInt(s, 10, bits)); null and the string "null" leave the field unchanged.
func QuotedInt(b []byte, i uint64, max uint64) (int64, uint64, uint64) {
	j, c := At(b, i)
	k := ValueEnd(b, j)
	if c == 'n' {
		return 0, Keep, k
	}
	if c != '"' {
		return 0, TypeErr, k
	}
	noEscape(b, j+1, k-1)
	if k-j == 6 && b[j+1] == 'n' && b[j+2] == 'u' && b[j+3] == 'l' && b[j+4] == 'l' {
		return 0, Keep, k
	}
	return signed(b, j+1, k-1, max, true), statusOf(b, j+1, k-1, max, true), k
}

// signedParts splits b[i:j] into its sign and digits: (negative, the index of the first digit,
// ok). A '-' is allowed; a '+' only if plus (strconv.ParseInt's syntax; a JSON number has none).
func signedParts(b []byte, i uint64, j uint64, plus bool) (bool, uint64, bool) {
	if i >= j {
		return false, i, false
	}
	if b[i] == '-' {
		return true, i + 1, true
	}
	if b[i] == '+' {
		return false, i + 1, plus
	}
	if !isDigit(b[i]) {
		return false, i, false
	}
	return false, i, true
}

// statusOf is Set if b[i:j] is a signed integer in [-max-1, max] (signedParts' syntax, then
// Digits), else TypeErr.
func statusOf(b []byte, i uint64, j uint64, max uint64, plus bool) uint64 {
	neg, d, ok := signedParts(b, i, j, plus)
	if !ok {
		return TypeErr
	}
	lim := max
	if neg {
		lim = max + 1
	}
	_, ok2 := Digits(b, d, j, lim)
	if !ok2 {
		return TypeErr
	}
	return Set
}

// signed is the value of b[i:j] when statusOf says Set (else 0).
func signed(b []byte, i uint64, j uint64, max uint64, plus bool) int64 {
	neg, d, ok := signedParts(b, i, j, plus)
	if !ok {
		return 0
	}
	lim := max
	if neg {
		lim = max + 1
	}
	m, ok2 := Digits(b, d, j, lim)
	if !ok2 {
		return 0
	}
	if neg {
		// -m, also for m = max+1 (the smallest value)
		return -int64(m-1) - 1
	}
	return int64(m)
}

// String decodes the value at or after i into a string.
func String(b []byte, i uint64) (string, uint64, uint64) {
	j, c := At(b, i)
	if c == '"' {
		s, k := Str(b, j)
		return s, Set, k
	}
	k := ValueEnd(b, j)
	if c == 'n' {
		return "", Keep, k
	}
	return "", TypeErr, k
}

// Bool decodes the value at or after i into a bool.
func Bool(b []byte, i uint64) (bool, uint64, uint64) {
	j, c := At(b, i)
	k := ValueEnd(b, j)
	if c == 't' {
		return true, Set, k
	}
	if c == 'f' {
		return false, Set, k
	}
	if c == 'n' {
		return false, Keep, k
	}
	return false, TypeErr, k
}
