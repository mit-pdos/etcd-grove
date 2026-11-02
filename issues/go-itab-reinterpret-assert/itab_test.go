// The reproduction of the golang/go issue: an interface value read through a
// *I1-to-*I2 conversion (legal without unsafe: I1 and I2 have identical
// underlying types) has dynamic type T, yet x.(T), a type switch, == and a map
// lookup all miss it. Run in any module: go test -run TestItabReinterpret -v
package itab

import "testing"

type I1 interface{ M() }
type I2 interface{ M() }

type T struct{ x int }

func (T) M() {}

func TestItabReinterpret(t *testing.T) {
	var a I1 = T{1}
	b := *(*I2)(&a) // *I1 converts to *I2: identical underlying types
	var c I2 = T{1}

	if any(b) != any(c) {
		t.Fatalf("setup: any(b) != any(c)")
	}
	if _, ok := b.(T); !ok {
		t.Errorf("b.(T) fails although b's dynamic type is %T", b)
	}
	switch b.(type) {
	case T:
	default:
		t.Errorf("a type switch on b misses case T")
	}
	if b != c {
		t.Errorf("b == c is false although any(b) == any(c)")
	}
	if _, ok := map[I2]int{c: 1}[b]; !ok {
		t.Errorf("a map[I2] lookup of b misses the key c")
	}
	func() {
		defer func() {
			if r := recover(); r != nil {
				t.Errorf("b.(T) panics: %v", r)
			}
		}()
		_ = b.(T)
	}()
}

// The value conversion recomputes the itab (golang/go#18595): this passes.
func TestItabValueConversion(t *testing.T) {
	var a I1 = T{1}
	b := I2(a)
	if _, ok := b.(T); !ok {
		t.Errorf("I2(a).(T) fails")
	}
}
