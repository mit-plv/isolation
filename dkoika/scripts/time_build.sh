#! /bin/sh
dune build deps/koika/coq
dune build deps/koika/examples/rv_isolation
dune build deps/koika/examples/rv_cache_isolation
dune build src/koika
# time dune build src/koikaExamples/Enclaves
# time dune build src/koikaExamples/EnclaveWithCache
