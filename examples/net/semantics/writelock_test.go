//go:build linux

package semantics

import (
	"bytes"
	"errors"
	"net"
	"sync"
	"testing"
	"time"
)

// v3.3, D25: Go's write lock (notes/dsverify-net-port-plan.md, phase 2).

// TestWriteLock (D25: concurrent Writes on one end do not interleave: Go's
// poll.FD.Write takes fd.writeLock() before its loop and releases it after,
// internal/poll/fd_unix.go). Writers on one end, each a distinct 4 MiB
// buffer (far more than the socket buffers: each Write takes many write(2)
// steps), start together against a slow reader; the reader sees each buffer
// contiguous, in some order, and every Write returns its whole length.
// Without the lock the steps of two Writes could interleave in the byte
// stream (the model before v3.3 allowed it). Also: a Write waiting for the
// lock when another goroutine Closes the end returns ErrClosed with 0 bytes
// (fdMutex.rwlock fails once the fd is closing; the waiters are woken by
// increfAndClose at once, so the waiter may return before or after the
// holder: both orders measured by the v3.3 review, and both allowed by the
// model, where the holder's failing step precedes the waiter's). Measured.
func TestWriteLock(t *testing.T) {
	t.Parallel()
	const writers, size = 4, 4 << 20
	d, a := pair(t)
	bufs := make([][]byte, writers)
	for i := range bufs {
		bufs[i] = bytes.Repeat([]byte{byte('A' + i)}, size)
	}
	var wg sync.WaitGroup
	start := make(chan struct{})
	for i := range bufs {
		wg.Add(1)
		go func(b []byte) {
			defer wg.Done()
			<-start
			if n, err := d.Write(b); n != len(b) || err != nil {
				t.Errorf("Write = %d, %v; want %d, nil", n, err, len(b))
			}
		}(bufs[i])
	}
	close(start)
	got := make([]byte, 0, writers*size)
	buf := make([]byte, 64<<10)
	a.SetReadDeadline(time.Now().Add(10 * guard))
	for len(got) < writers*size {
		time.Sleep(50 * time.Microsecond) // a slow reader
		n, err := a.Read(buf)
		got = append(got, buf[:n]...)
		if err != nil {
			t.Fatalf("Read after %d bytes: %v", len(got), err)
		}
	}
	wg.Wait()
	seen := map[byte]bool{}
	for i := 0; i < writers; i++ {
		run := got[i*size : (i+1)*size]
		c := run[0]
		if seen[c] || bytes.Count(run, []byte{c}) != size {
			t.Fatalf("buffer %d of the stream is not one Write's bytes contiguous (starts %q)", i, c)
		}
		seen[c] = true
	}

	// a Write waiting for the lock, the end closed meanwhile
	d2, _ := pair(t)
	big := make([]byte, 64<<20)
	first := make(chan error, 1)
	second := make(chan [2]any, 1)
	go func() { _, err := d2.Write(big); first <- err }()
	time.Sleep(100 * time.Millisecond) // the first Write blocks, holding the lock
	go func() { n, err := d2.Write([]byte("second")); second <- [2]any{n, err} }()
	time.Sleep(100 * time.Millisecond) // the second waits for the lock
	d2.Close()
	if err := <-first; !errors.Is(err, net.ErrClosed) {
		t.Fatalf("holder's Write = %v; want ErrClosed", err)
	}
	r := <-second
	if n, err := r[0].(int), r[1]; n != 0 || !errors.Is(err.(error), net.ErrClosed) {
		t.Fatalf("waiter's Write = %d, %v; want 0, ErrClosed", n, err)
	}
}
