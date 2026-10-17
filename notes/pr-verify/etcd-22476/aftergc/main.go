package main

import (
	"fmt"
	"runtime"
	"time"
)

func heap() uint64 { var m runtime.MemStats; runtime.GC(); runtime.ReadMemStats(&m); return m.HeapInuse }

func main() {
	ready := make(chan struct{})
	close(ready)
	b := heap()
	for i := 0; i < 1_000_000; i++ {
		select {
		case <-time.After(time.Hour):
		case <-ready:
		}
	}
	fmt.Printf("abandoned time.After x1e6: heap grew %d KiB\n", (int64(heap())-int64(b))/1024)
	// control: keep the channels referenced
	b = heap()
	keep := make([]<-chan time.Time, 0, 1_000_000)
	for i := 0; i < 1_000_000; i++ {
		keep = append(keep, time.After(time.Hour))
	}
	fmt.Printf("referenced time.After x1e6: heap grew %d KiB (len %d, slice itself ~7812 KiB)\n", (int64(heap())-int64(b))/1024, len(keep))
	runtime.KeepAlive(keep)
}
