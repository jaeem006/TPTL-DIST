# tptl-dist in Agda

An Agda formalisation of **tptl-dist**, a sequent calculus for an extension of
Timed Propositional Temporal Logic (TPTL) for reasoning about real-time
distributed systems. It includes the syntax, the semantics, the soundness of the
rules, and automation that proves sequents and rules of the calculus.

The calculus and its soundness are described in:

> *A sequent calculus for tptl-dist* (FORTE),
> <https://vrahli.github.io/articles/tptl-calc-forte.pdf>

## Requirements

- Agda 2.6.3
- The Agda standard library v2.0

To check everything, including the examples:

```sh
agda -i . -i <path-to-stdlib>/src Examples.lagda
```

## Files

**Core**

| File | Contents |
|---|---|
| `World.lagda`, `WorldUtil.lagda` | Worlds (time structures) and lemmas about them |
| `Syntax.lagda` | Formulas, resources (time expressions), contexts and sequents |
| `Semantics.lagda` | Models and satisfaction; validity of sequents and rules |
| `Subst.lagda` | Weakening and substitution, and their semantic lemmas |
| `Decidable.lagda` | Decidable equality on the syntax |
| `Misc.lagda` | Auxiliary lemmas |

**Rules and their soundness**

| File | Contents |
|---|---|
| `RulesProp.lagda`, `RulesNonEmpty.lagda` | Propositional rules |
| `RulesPred.lagda`, `RulesMisc.lagda` | Predicate-logic rules |
| `RulesTemp.lagda` | Temporal rules |
| `RulesInd.lagda`, `RulesClassical.lagda` | Induction and classical rules |
| `Rules.lagda` | Further rules, with their soundness proofs |

**Automation**

| File | Contents |
|---|---|
| `Automation.lagda` | Inductive derivations `⊢`, their soundness (`sound`), and a fuel-bounded proof search `decidable⊢` |
| `Plug.lagda` | `plug-⊢`: instantiates a closed derivation and plugs it into an arbitrary context; `hyps→rule` |
| `ProveTactic.lagda` | Reflection macros `prove n` (for sequents) and `prove-rule n` (for rules) |
| `Examples.lagda` | The same examples proved with both approaches |

## Automation in a nutshell

The search works on closed sequents. To prove a statement that mentions
arbitrary Agda formulas, time expressions or contexts, there are two
approaches:

1. **Reflection** (`prove n`): abstract the opaque formulas to variables, run
   the search, put the formulas back in the derivation, and let Agda re-check it.
2. **Substitution** (`plug-⊢`, `prove-rule n`): run the search on an abstract
   sequent, then instantiate the derivation using the generic lemma `plug-⊢`.
   This also works through binders. For example, rule ◇↓R is proved with
   `prove-rule 10`.

Both approaches are proof-producing: the search and the macros need not be
trusted, since Agda checks every derivation they produce.

## Use of AI tools

Parts of this development were written with the help of an AI coding
assistant (Claude Code, by Anthropic). This includes parts of: the
proof search in `Automation.lagda`, the instantiation lemmas in
`Plug.lagda`, the reflection macros in `ProveTactic.lagda`, and the
examples in `Examples.lagda`. All of this was directed and reviewed by
the authors. The automation uses no postulates and no `TERMINATING`
pragmas, so its correctness does not depend on trusting the tool: Agda
checks every proof.
