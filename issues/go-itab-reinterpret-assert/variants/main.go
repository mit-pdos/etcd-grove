// Which conversions keep the old itab (pointer) and which recompute it (value,
// golang/go#18595): go run variants/main.go
package main

import "fmt"

type I interface{ M() }
type J I
type T struct{ x int }

func (T) M() {}

func main() {
	var a I = T{1}

	v := J(a) // value conversion: itab recomputed (golang/go#18595)
	_, ok := v.(T)
	fmt.Println("J(a).(T) ok:", ok)

	p := *(*J)(&a) // pointer conversion: itab of (T, I) kept
	_, ok = p.(T)
	var c J = T{1}
	fmt.Println("(*J)(&a) .(T) ok:", ok, " == J(T{1}):", p == c)

	u := *(*interface{ M() })(&a) // unnamed interface, as in #18595
	_, ok = u.(T)
	var w interface{ M() } = T{1}
	fmt.Println("(*interface{M()})(&a) .(T) ok:", ok, " == :", u == w)
}
