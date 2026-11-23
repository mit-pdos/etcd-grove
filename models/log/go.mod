// The model of a standard-library package (log/slog): the package's Go source as the model changes
// it, built only in place of the real package (models/goroot.py: a `go build -overlay` file, or a
// GOROOT of links for goose). This module is never built; it keeps these files out of models.lab's
// `./...`, where they would not compile as a package of their own path.
module models.lab/stdmodels/log

go 1.27
