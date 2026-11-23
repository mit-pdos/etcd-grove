package main

import (
	"fmt"

	_ "a.example/randprobe/early"
	"github.com/google/uuid"
)

func main() {
	_, err := uuid.NewRandom()
	fmt.Printf("NewRandom error: %v\n", err)
	defer func() { fmt.Printf("New panicked: %v\n", recover() != nil) }()
	uuid.New()
}
