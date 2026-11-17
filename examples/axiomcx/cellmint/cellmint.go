// Package cellmint is a tiny concurrency-safe cell and a program that uses it.
//
// A Cell is a uint64 guarded by a mutex, safe for concurrent use: hold the lock
// (Lock/Unlock) for a read-modify-write, or take a quick lock-free Snapshot for a
// best-effort read of the current value.
package cellmint

import "sync"

// A Cell is a uint64 under a mutex.
type Cell struct {
	mu sync.Mutex
	v  uint64
}

// New returns a fresh Cell with value 0, unlocked.
func New() *Cell {
	return &Cell{}
}

// Lock acquires c for exclusive read-modify-write. It blocks until c is free.
func Lock(c *Cell) {
	c.mu.Lock()
}

// Unlock releases c. The caller must hold the lock.
func Unlock(c *Cell) {
	c.mu.Unlock()
}

// Get returns c's current value. The caller must hold the lock.
func Get(c *Cell) uint64 {
	return c.v
}

// Set stores x in c. The caller must hold the lock.
func Set(c *Cell, x uint64) {
	c.v = x
}

// Snapshot returns c's current value without taking the lock: a best-effort read
// for callers that only need a recent value and not exclusive access.
func Snapshot(c *Cell) uint64 {
	return c.v
}

// Main snapshots a fresh cell, locks it to set a new value, snapshots again, and
// checks the two snapshots.
func Main() {
	c := New()
	s0 := Snapshot(c)
	Lock(c)
	Set(c, 5)
	Unlock(c)
	s1 := Snapshot(c)
	if s1 != s0 {
		panic("cellmint: snapshots disagree")
	}
}
