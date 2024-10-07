===============================================================================
MTIsolation
===============================================================================

This repository contains the Coq-SMT toolchain and proofs of the examples from the CCS'24 `Specification and Verification of Strong Timing Isolation of Hardware Enclaves <https://people.csail.mit.edu/stellal/papers/isolation-CCS24.pdf>`_ paper. The evaluated artifact and Docker image associated with the paper is available at `https://zenodo.org/records/12786597 <https://zenodo.org/records/12786597>`_.


Getting started
===============

Installing dependencies and building from source
------------------------------------------------

* OCaml 4.14, `opam <https://opam.ocaml.org/doc/Install.html>`_ 2.0 or later, GNU make
* Coq 8.18::

    opam install coq=8.18.0

* Dune 3.12 or later::

    opam upgrade dune

* Z3 4.12 or later::
    
    opam install z3 
  
* Some OCaml packages::

    opam install base cmdliner core core_unix hashcons menhir parsexp ppx_deriving ppx_import stdio zarith 

* To run the tests of the RISCV core, a `RISCV compilation toolchain <https://github.com/xpack-dev-tools/riscv-none-embed-gcc-xpack/releases/>`_.

* To run C++ simulations: a recent C++ compiler (clang or gcc) and
  ``libboost-dev``.

* To run Verilog simulations: ``Verilator``

For reproducibility, here is one set of versions known to work:
- OCaml 4.14.0 with::
 
  opam install base=v0.16.3 cmdliner=1.2.0 coq=8.18.0 core=v0.16.2 core_unix=v0.16.0 dune=3.12.1 hashcons=1.3 menhir=20230608 parsexp=v0.16.0 ppx_deriving=5.2.1 ppx_import=1.10.0 stdio=v0.16.0 zarith=1.13 z3=4.12.4

Git submodules are used for |koika| and the source of the RISC-V examples. If you did not clone with ``--recursive``, run::

    git submodule update --init --recursive

You can compile the full distribution, including examples, tests, and proofs by running ``make`` in the ``dkoika/`` directory of this repo. 

Organization
============

.. _repo-map:

.. begin repo architecture

|koika| and examples
--------------------
The examples in the paper are written on top of the reference implementation of |koika| (apart from the resource isolation example, which is written directly in `dKôika <dkoika_>`_). See ``dkoika/deps/koika/README.rst`` for details about |koika|, its reference implementation, verified compiler, and C++ simulator Cuttlesim.

The main RISC-V enclave example is in ``dkoika/deps/koika/examples/rv_isolation/``:

- ``rv32.v``: top-level design, used to generate verilog and C++ for simulation.
- ``Machine.v``: our example consists of two RISC-V cores, a security monitor, and memory arbiter.
- ``RVCore.v``: 4-stage pipelined RISC-V core, with a custom instruction for enclaves and secure purging
- ``Memory.v``: round-robin memory arbiter
- ``SecurityMonitor.v``: security monitor 
- ``tests/``: contains RISC-V, C, and enclave tests (``enclaves/``)

The tests can be run with Cuttlesim with ``make cuttlesim-tests`` and with Verilator with ``make verilator-tests``.

The extension with caches is in ``dkoika/deps/koika/examples/rv_cache_isolation/``, with a similar directory structure to ``rv_isolation/``. The modifications are primarily in ``Memory.v``.

|dkoika| and symbolic language 
------------------------------
.. _dkoika:

|dkoika| is an implementation of |koika| designed for verification and static analysis. It is syntactically and semantically very similar to the reference implementation. We translate our RISC-V examples into |dkoika| and then use verified static analyses to translate into a *modular* |dkoika| semantics. 

|dkoika| is accompanied with a symbolic assertion language, used to generate SMT assertions and then reflected back into Coq props for use in proofs. A verified preprocessing step adds typing and debugging annotations for use in SMT.

``dkoika/src/koika/``
  - ``Syntax.v``: Syntax of |dkoika|.
  - ``Semantics.v``: Semantics of |dkoika|.
  - ``Symbolic.v``: Symbolic assertion language used for SMT. A ``file_t``, which contains the |dkoika| machine and pre- and post-conditions, is extracted for |smtkoika|.
  - ``SymbolicInterp.v``: Symbolic assertion language interpretation and helper functions
``dkoika/src/koikaExamples/KoikaConversion.v``: transpiler from |koika| to |dkoika|

|smtkoika| 
---------
|smtkoika| translates a |koika| machine together with symbolic assumptions and assertions into a (single-cycle) SMT query, checked using Z3. The solver returns ``UNSAT :)`` if the assertions hold and ``SAT :(`` if the assertions do not hold, along with a counterexample that the proof developer can query. If the assumptions are false, |smtkoika| will fail with ``Assumes are false``. 

To check an individual file, run::

  > cd smt_koika/src
  > ./build_file.sh <your-extracted-file>.ml
  > ../_build/default/src/main.exe -o debug.txt -q 

The optional ``-o`` flag outputs a counterexample (if one is found) along with failed assertions, for debugging. The optional ``-q`` flag provides a query interface for inspecting counterexamples.

``smt_koika/src/``:
  - ``koika_smt.ml``: SMT translation of |koika|.
  - ``query_*``: query language to inspect and debug counterexamples at each rule.

Isolation specs and proofs
--------------------------
This repo contains proofs of strong timing isolation for three examples: the main RISC-V enclave example, a cache extension, and a demo resource isolation example.

``dkoika/src/koikaExamples/{Enclaves,EnclaveWithCache,ResourceIsolation}``
  - ``Spec.v``: strong timing isolation specification, expressed as a state machine.
  - ``Impl.v``: implementation machine with model of external memory.
  - ``Theorem.v``: top-level theorem expressing trace equivalence of the implementation and specification for an arbitrary number of cycles.
  - ``Proof.v``: proof of the theorem. The ``Print Assumptions`` line at the end prints out all Coq assumptions the proof relies on (i.e. the SMT assertions hold).
  - ``SMT_*.v``: generates files for |smtkoika|.

The SMT assertions can be checked by running, for example::

  > cd smt_koika
  > ./scripts/time_smt.sh ../dkoika/_build/default/{out_Enclaves,EnclaveWithCache}


.. end repo architecture

Case studies in the paper
=========================
- The main RISC-V enclave example is in ``dkoika/deps/koika/examples/rv_isolation``, with the proof in ``dkoika/src/koikaExamples/Enclaves``
- The cache extension is in ``dkoika/deps/koika/examples/rv_cache_isolation`` (the main changes from ``rv_isolation`` are in ``Memory.v``) with the proof in ``dkoika/src/koikaExamples/EnclaveWithCache``
- The branch predictor modification is in ``dkoika/deps/koika/examples/rv_isolation`` of the branch ``branch-predictors``, with the proof in ``dkoika/src/koikaExamples/Enclaves``
- The resource isolation example is in ``dkoika/src/koikaExamples/ResourceIsolation`` of the branch ``resource_isolation``. It is implemented entirely in |dkoika| and verified in Coq (without SMT), making use of various verified static analyses and a CPS-semantics.

Summary proof strategy
======================
1.  Write a spatially and temporally partitioned implementation with observation function, in an HDL with formal semantics.
2.  Write a specification state machine with observation function, instantiated with spatial partitions of the implementation.
3.  State strong isolation theorem: trace equivalence.
4.  State per-cycle implementation, specification, and simulation invariants and postconditions, decomposed into per-module assertions when convenient. Implementation postconditions may include reaching and maintaining a state functionally equivalent to a new machine when context switching. Specification invariants may include asserting that the enclave machines enforce the enclave programming model. Simulation invariants define equivalence between the implementation and specification.
5.  Prove invariants are preserved and postconditions hold at each cycle, using SMT where possible in an assertion-based verification style.
6.  Prove soundness of the metatheory and reduction to single-cycle verification in Coq, including reasoning about any external models such as memory or MMIO.

  

.. |koika| replace:: Kôika
.. |dkoika| replace:: dKôika
.. |smtkoika| replace:: SMT-Kôika
