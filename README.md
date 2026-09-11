# LeanUtils
Lean scripts for indexing sorries and verifying proofs.

Three executables, all dependency-free and driven from the command line with
JSON in and JSON out:

| binary | purpose |
|---|---|
| `ExtractSorry <file>` | list every `sorry` in a file with its goal and position |
| `KernelCheck <file> <sorry> <term>` | check a candidate proof term against the goal of one `sorry` |
| `ExtractGoal <file> <sorry> [flags]` | restate the goal of one `sorry` as a standalone theorem |

```bash
lake build
lake test        # #guard_msgs golden tests in LeanUtilsTest/
```

Each binary re-elaborates the given file, so the project it belongs to must
already be built (`lake build` in that project) and the binary must run with a
Lean toolchain matching the project's `lean-toolchain`. Run it from the
project's root, or under `lake env`, so that `LEAN_PATH` is available; the
search path is otherwise reconstructed by walking the project's `.lake`
directories.

## The sorry record

`ExtractSorry` prints one record per `sorry` token:

```json
{"parentDecl": "test",
 "location": {"start_line": 6, "start_column": 2, "start_byte": 86,
              "end_line": 6, "end_column": 7, "end_byte": 91},
 "kind": "tactic",
 "hash": 3234805056349482567,
 "goal": "someLemma : True\n⊢ 1 + 1 = 2"}
```

`start_byte`/`end_byte` are the token's byte range, which is what a tool that
rewrites the source needs to splice at. `kind` is `"tactic"` or `"term"`: a
replacement in tactic position needs no leading `by`, one in term position does.
A `sorry` tactic also elaborates to a `sorry` term at the same position; the two
are merged into the tactic record. A token that closes several goals
(`constructor <;> sorry`) yields one record per goal, distinguished by `goal`.

`KernelCheck` and `ExtractGoal` take a record back as their second argument, in
the shape the `ParsedSorry` structure deserializes:

```json
{"goal": "someLemma : True\n⊢ 1 + 1 = 2",
 "startPos": {"line": 6, "column": 2}, "endPos": {"line": 6, "column": 7},
 "parentDecl": "test", "hash": "3234805056349482567",
 "kind": "tactic", "startByte": 86, "endByte": 91}
```

`hash` is a decimal string here (a JSON number cannot carry a full `UInt64`).
`kind`, `startByte` and `endByte` are optional; without `kind` both term and
tactic nodes are accepted. `goal` is only consulted when one token closes
several goals, to select the intended one.

## ExtractGoal

Turns the goal at a `sorry` into a theorem that can be stated on its own, plus
the term that closes the original goal with it. The local context at the sorry
is reverted into binders, so the theorem is exactly the goal with its context
quantified; the proof is left as `sorry` for whoever wants to prove it.

```
$ ExtractGoal LeanUtilsTest/LeanFileWithSorries.lean '{"goal": "...", "startPos": {"line": 6, "column": 2}, ...}'
{"ok":
 "import Lean\n\n
  -- sorrydb-helper-start\n
  theorem mytheorem (someLemma : True) : 1 + 1 = 2 := sorry\n
  -- sorrydb-application: mytheorem someLemma"}
```

The payload has three parts separated by the two marker lines: the file's
source up to the start of the enclosing command (the helper belongs before
it, together with any `… in` wrappers, which are reproduced after the
marker), the helper theorem, and the application term. Replacing the original
`sorry` by `exact <application>` (or `by exact …` in term position) and
inserting the helper before the enclosing command yields a file whose only new
`sorry` is the helper's; the caller compiles that file to validate the
restatement. Universe parameters are renamed `sorrydb_u_1, …` so they cannot
collide with section universes at the insertion point.

The contract has three refusals, each reported as `{"error": "..."}`:

* `compact theorem signature contains omitted terms (⋯)` — a proof inside a
  data value was elided by the pretty printer and the statement would not
  re-elaborate; see `--show-proofs` and `--abstract-proofs`.
* `its type depends on an earlier sorry` — the goal mentions a `sorryAx`
  from another sorry; no restatement can name that term.
* `Found more than one goal` / `Found different types for infotrees` — the
  token closes several goals and the record's `goal` matches none of them.

### Rendering flags

The default rendering is the compact one (`pp.proofs` off, notation on). Each
flag changes one pretty-printer or context-handling decision; callers typically
try the default first and add flags only when the restatement fails to
elaborate.

| flag | effect |
|---|---|
| `--analyze` | render the application with `pp.analyze`: named arguments (`(d := d)`) for implicits the call site cannot infer |
| `--sanitize-context` | turn `let`-bound proofs into hypotheses; clear locals whose type or value mentions `sorryAx`, unused `let`s, and unused inaccessible locals |
| `--assumption-holes` | an argument whose value is an inaccessible local renders as `?_`; replace it by `(by assumption)` |
| `--expr-signature` | render the statement from the type expression (`name : ∀ …`) instead of `MessageData.signature`, so the flags below can act on it |
| `--no-fun-binder-types` | `pp.funBinderTypes := false` |
| `--no-coercion-types` | `pp.coercions.types := false` (drop `⇑f : A → B` ascriptions) |
| `--no-field-notation` | `pp.fieldNotation := false` (`X.ρ` can re-resolve to the wrong constant through an `abbrev`) |
| `--coe-explicit` | print `DFunLike.coe (F := …)` explicitly |
| `--numeric-types` | `pp.numericTypes := true` (`(2 : ℝ)`) |
| `--show-proofs` | `pp.proofs := true` on the statement: proofs nested in data print instead of `⋯` (lossless by proof irrelevance) |
| `--abstract-proofs` | hoist closed `Prop`-typed subterms of the goal into binders `sorrydb_prf_i`, `_` at the call site; only `Prop`s, so the statement stays equivalent |

### Flag combinations that have worked

The flags are independent, but not every combination is meaningful, and the
useful ones form an escalation ladder: start compact, and add flags only when
the previous rendering failed to elaborate at the insertion point. This is the
order used to convert the SorryDB evaluation split (about 590 sorries across
~100 projects); the last column says how often each rung was the first one to
succeed there.

| rung | flags | fixes | share |
|---|---|---|---|
| 1 | *(none)* | — | ~94% |
| 2 | `--sanitize-context` | context polluted by `let`s, `sorryAx`-tainted or inaccessible locals | ~5% |
| 3 | `--analyze` | call site fails with *don't know how to synthesize implicit argument* | <1% |
| 4 | `--analyze --assumption-holes` | the call has `?_` holes for inaccessible locals | <1% |
| 5 | `--analyze --expr-signature --no-fun-binder-types --no-field-notation` | statement fails to elaborate: forced `fun (a : T) ↦` ascriptions, `X.f` resolving to the wrong constant | <1% |
| 6 | rung 5 `+ --no-coercion-types` | `⇑f : A → B` ascriptions losing the bundled hom's implicits | rare |
| 7 | `--analyze --expr-signature --coe-explicit` | typeclass problem stuck on a coercion | rare |
| 8 | rung 5 `+ --numeric-types` | numerals defaulting to the wrong type (`-1` becoming `ℤ`) | rare |
| 9 | rung 5 `+ --show-proofs` | *omitted terms (⋯)*: a proof nested in a data value | rare |
| 10 | `--analyze --abstract-proofs`, optionally with the rung-5 flags or `--show-proofs` | *omitted terms* or *depends on an earlier sorry* where the offending subterm is a closed `Prop` | rare |

Notes:

* Rungs 5–10 need `--expr-signature`: the default signature printer works on
  the bare constant, so `pp.*` flags and `pp.analyze` have nothing to act on
  there. `--coe-explicit` switches `pp.analyze` on by itself.
* `--assumption-holes` and `--abstract-proofs` only matter when the call
  contains `?_`; the first substitutes `(by assumption)`, the second `_`,
  which unification fills with the original proof.
* Later rungs often render the same text as an earlier one (e.g. `--analyze`
  changes nothing when no implicit needs naming). Comparing renderings before
  compiling avoids paying for a duplicate.
* Rung 9 is the one that recovers most *omitted terms* refusals; fully
  explicit printing (`pp.all`) recovers no more than it does and produces
  statements 2–35× larger, so it is not offered as a flag.
* When one token closes several goals, the application closes only the goal
  the record names. The caller has to keep the siblings as sorries, e.g. by
  splicing `first | exact <application> | sorry`; that is a splice decision,
  not a rendering flag.

## KernelCheck

Elaborates the term against the goal in the sorry's own local context, rejects
terms that mention a banned constant (`sorryAx`) by name, and otherwise asks
the kernel to accept the declaration:

```
$ KernelCheck LeanUtilsTest/LeanFileWithSorries.lean '{"goal": "⊢ True", ..., "parentDecl": "test", "hash": "1590982770643673912"}' trivial
{"success": true, "error": null}
```

## Toolchains

`lean-toolchain` pins the version the tests run with. The sources are kept
free of version-specific API where possible (see `LeanUtils/Backports.lean`)
and have been built against Lean 4.17 through the 4.27 release candidates.
