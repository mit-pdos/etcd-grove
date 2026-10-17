package main

import "fmt"

func main() {
	bad := 0
	first := -1
	for x := 1; x <= 100000000; x++ {
		a := int(float64(x) * 0.8)
		b := x * 4 / 5
		if a != b {
			bad++
			if first < 0 {
				first = x
			}
		}
	}
	fmt.Println("mismatches in 1..1e8:", bad, "first:", first)
}
