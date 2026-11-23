// randprobe: a program in which a package initialized before github.com/google/uuid assigns
// crypto/rand.Reader (Go >= 1.21 initializes ready packages in import-path order: a.example/...
// before github.com/...). Outside the uuid model's premise (the program never assigns
// crypto/rand.Reader): run.sh shows v1.3.1's New panicking here, and the model's not.
module a.example/randprobe

go 1.27

require github.com/google/uuid v1.3.1
