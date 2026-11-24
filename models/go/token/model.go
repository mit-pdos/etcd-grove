// The Go model of go/token's IsExported (token.go, Go 1.27.3), the one declaration
// Net/Code/go/token.toml's [model] table replaces; the net/rpc model's register calls it on a
// service's name.

package token

import (
	"internal/gomodel"
	"unicode/utf8"
)

// MODEL: IsExported is, in Go, `ch, _ := utf8.DecodeRuneInString(name); return
// unicode.IsUpper(ch)`. The model gives Go's result wherever the name's first byte is ASCII, and any result otherwise:
//   - The empty name: DecodeRuneInString returns RuneError (U+FFFD), which is not upper case, so
//     Go returns false, as the model does.
//   - A first byte c < utf8.RuneSelf (0x80): DecodeRuneInString returns rune(c) (its fast path),
//     and IsUpper of a rune <= MaxLatin1 is properties[uint8(r)]&pLmask == pLu
//     (unicode/letter.go), which for c < 0x80 holds exactly of 'A'..'Z' (unicode/tables.go's
//     properties table). The model returns 'A' <= c && c <= 'Z'.
//   - Any other first byte: Go's result is IsUpper of the decoded rune (RuneError for an invalid
//     encoding) and depends on Unicode's case tables. The model returns gomodel.Choose(), any
//     boolean, which covers both of Go's possible results.
//
// It reads no package variable, which is why it stands in for Go's code: that code is
// translatable (goose translates it, with unicode's tables), but IsUpper reads unicode's tables
// and DecodeRuneInString's slow path reads utf8's, so a proof of Go's code needs those packages'
// initialization, which IsExported's spec does not take.
func IsExported(name string) bool {
	if len(name) == 0 {
		return false
	}
	c := name[0]
	if c < utf8.RuneSelf {
		return 'A' <= c && c <= 'Z'
	}
	return gomodel.Choose()
}
