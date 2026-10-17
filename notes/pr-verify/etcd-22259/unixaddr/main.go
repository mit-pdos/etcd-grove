package main

import (
	"fmt"
	"net"
	"os"
	"path/filepath"
)

func main() {
	p := filepath.Join(os.TempDir(), "ua.sock")
	os.Remove(p)
	l, err := net.Listen("unix", p)
	if err != nil { panic(err) }
	go func() { c, _ := net.Dial("unix", p); _ = c }()
	c, err := l.Accept()
	if err != nil { panic(err) }
	ra := c.RemoteAddr()
	fmt.Printf("remote nil=%v %T %q\n", ra == nil, ra, func() string { if ra == nil { return "" }; return ra.String() }())
}
