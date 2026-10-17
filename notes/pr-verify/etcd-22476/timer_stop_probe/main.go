package main

import (
	"fmt"
	"time"
)

func main() {
	f := 0
	for i := 0; i < 100000; i++ {
		t := time.NewTimer(0)
		if i%100 == 0 {
			time.Sleep(10 * time.Microsecond)
		}
		if !t.Stop() {
			f++
		}
	}
	fmt.Println("Stop() == false:", f, "of 100000")
	// once stopped, a receive blocks
	t := time.NewTimer(0)
	time.Sleep(time.Millisecond)
	fmt.Println("after 1ms, Stop():", t.Stop())
	select {
	case <-t.C:
		fmt.Println("received a value after Stop")
	case <-time.After(100 * time.Millisecond):
		fmt.Println("no value after Stop: a bare <-t.C would block forever")
	}
}
