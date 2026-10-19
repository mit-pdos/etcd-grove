// The reproduction of the golang/go issue drafted in
// issues/upstream/go-itab-reinterpret-assert/issue.md: go run main.go
package main

import "fmt"

type I1 interface{ M() }
type I2 interface{ M() }

type T struct{ x int }

func (T) M() {}

func main() {
	var a I1 = T{1}
	b := *(*I2)(&a) // *I1 converts to *I2: identical underlying types
	var c I2 = T{1}

	_, ok := b.(T)
	fmt.Println(ok)               // false
	fmt.Println(b == c)           // false
	fmt.Println(any(b) == any(c)) // true
	fmt.Printf("%T\n", b)         // main.T
	_ = b.(T)                     // panics
}
