// More consequences of the reinterpretation in ../main.go: go run probe/main.go
package main

import "fmt"

type I1 interface{ M() }
type I2 interface{ M() }
type T struct{ x int }

func (T) M() {}

func try(name string, f func() any) {
	defer func() {
		if r := recover(); r != nil {
			fmt.Printf("%-28s panic: %v\n", name, r)
		}
	}()
	fmt.Printf("%-28s %v\n", name, f())
}

func main() {
	var a I1 = T{1}
	b := *(*I2)(&a)
	var c I2 = T{1}
	try("b.(T)", func() any { return b.(T) })
	try("_, ok := b.(T)", func() any { _, ok := b.(T); return ok })
	try("switch b.(type) case T", func() any {
		switch b.(type) {
		case T:
			return "T"
		default:
			return "default"
		}
	})
	try("b == c", func() any { return b == c })
	try("any(b) == any(c)", func() any { return any(b) == any(c) })
	try("map[I2]int{c:1}[b]", func() any { m := map[I2]int{c: 1}; v, ok := m[b]; return fmt.Sprint(v, ok) })
	try("b.(fmt.Stringer)", func() any { _, ok := b.(fmt.Stringer); return ok })
	try("any(b).(T)", func() any { return any(b).(T) })
	try("fmt %T", func() any { return fmt.Sprintf("%T", b) })
	b.M()
}
