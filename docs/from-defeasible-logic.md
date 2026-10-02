# Arriving from defeasible logic

- **Covers:** the defeasible logic vocabulary of Nute, Antoniou and Governatori, as
  SPINdle, Deimos and DR-Prolog implement it, mapped onto this one: facts, strict and
  defeasible rules, defeaters, the superiority relation, and the four proof tags. Also
  the one semantic difference that changes answers: a tie between two defaults is
  believed on both sides here, where defeasible logic concludes neither side.
- **Not here:** how blocking works → [exceptions.md](exceptions.md); how a clash is
  decided → [nmtms.md](nmtms.md); the modal attitudes → [belief.md](belief.md).
- **Assumes:** sentex, context, defeasible, defeat-class, dilemma →
  [glossary.md](glossary.md).

Most of a defeasible theory carries over one construct at a time. The superiority
relation is the exception. This engine has no priority between rules, and a priority is
written as an exception on the inferior rule. SPINdle's normalizer also removes
superiority and defeaters, by a transformation it runs before it infers anything. Read
[A tie is believed, not withheld](#a-tie-is-believed-not-withheld) before the tables,
because it changes what `ask?` returns.

## Word for word

| in defeasible logic | here | what changes |
|---|---|---|
| a theory `D = (F, R, >)` | the sentexes visible from a context | there is no separate theory object; one KB holds many contexts, and two contradictory theories coexist in two contexts → [contexts.md](contexts.md) |
| fact `→ bird(tweety)` | `(bird Tweety)` asserted `{:strength :monotonic}` | a bare `assert` is `:default`, which is defeasible. A defeasible-logic fact is indisputable, so it needs the option |
| strict rule `human(X) → mammal(X)` | `(set/forwardRule (implies (human ?x) (mammal ?x)))` | concludes `:monotonic`, capped at its weakest antecedent. A bare `implies` is backward-only → [inference.md](inference.md) |
| defeasible rule `mammal(X) ⇒ ¬flies(X)` | `(set/defaultRule (set/forwardRule (implies (mammal ?x) (not (flies ?x)))))` | concludes `:default` |
| defeater `heavy(X) ⇝ ¬flies(X)` | `(exceptWhen (heavy ?x) <each rule concluding (flies ?x)>)` | an exception names one rule, not a literal ([below](#defeaters)) |
| superiority `r' > r` | `(exceptWhen <body of r'> r)` | an exception on the inferior rule ([below](#superiority-compiles-into-exceptwhen)) |
| `¬p` | `(not p)` | a stored sentex with its own handle, believed or not like any other |
| conflicting (mutually exclusive) literals | `disjoint`, `functional`, `asymmetric`, `irreflexive`, arity | each declaration forms a nogood the settle decides as it decides `p` against `(not p)` → [nmtms.md](nmtms.md#what-qualifies-as-a-nogood) |
| a rule with variables, read as its ground instances | `?x` | rules match first-order; nothing grounds a theory before inference |
| `+Δq` | `q` believed with defeat-class `:monotonic` | `(v/defeat-class kb h)` |
| `+∂q` | `q` believed with defeat-class `:default` | |
| `−∂q` | `q` not believed | `why-not` names the reason, `:excepted` or `:defeated` → [api.md](api.md) |
| `−Δq` | `q` not believed at `:monotonic` | |
| the conclusions of a theory | belief at a context | recomputed region-locally after every write, never by a full pass → [nmtms.md](nmtms.md#2-locality) |
| modal literal `BEL p`, `OBL p` | `(believes Agent p)` | a projection into the agent's context; no operator conversions and no modal logic → [belief.md](belief.md) |
| an XML or plain-text theory file | none | no reader for the format ships → [arriving.md](arriving.md#what-these-pages-are-not) |

## Facts and the strict part

A defeasible-logic fact is indisputable, and the equivalent here is an assertion at
`:monotonic`. A strict rule needs no strength of its own: a rule without
`set/defaultRule` confers `:monotonic`, capped at the weakest class among its
antecedents. Defeasible logic applies the same cap, because a strict rule over a `+∂`
premise yields only `+∂`:

```clojure
(v/assert kb '(set/forwardRule (implies (human ?x) (mammal ?x))) 'CxWell)
(v/assert kb '(human John) 'CxWell {:strength :monotonic})
(v/assert kb '(human Jane) 'CxWell)                          ; :default

(v/defeat-class kb (v/handle-of kb '(mammal John) 'CxWell))  ; => :monotonic   (+Δ)
(v/defeat-class kb (v/handle-of kb '(mammal Jane) 'CxWell))  ; => :default     (+∂)
```

A `:monotonic` conclusion defeats a `:default` one it contradicts, as `+Δ¬p` blocks
`+∂p`:

```clojure
(v/assert kb '(set/defaultRule (set/forwardRule (implies (bird ?x) (flies ?x)))) 'CxWell)
(v/assert kb '(bird Opus)         'CxWell {:strength :monotonic})
(v/assert kb '(not (flies Opus))  'CxWell {:strength :monotonic})

(v/ask? kb '(flies Opus) 'CxWell)      ; => false
(v/why-not kb '(flies Opus) 'CxWell)   ; => {:reason :defeated
                                       ;     :contradicted-by [{:sentence (not (flies Opus))
                                       ;                        :defeat-class :monotonic …}] …}
```

Two `:monotonic` sentences that contradict each other both stay believed, and the pair is
reported in `(v/conflicts kb)`. Defeasible logic leaves an inconsistent strict part
inconsistent too; neither system repairs it.

## A tie is believed, not withheld

Defeasible logic is skeptical. Given `quaker ⇒ pacifist` and `republican ⇒ ¬pacifist`
with no superiority between them, it concludes `−∂pacifist` and `−∂¬pacifist`. Under
ambiguity blocking, no rule whose body needs either literal fires.

This engine believes both sides at `:default` and reports the pair as a **dilemma**:

```clojure
(v/assert kb '(set/defaultRule (set/forwardRule (implies (quaker ?x) (pacifist ?x)))) 'CxWell)
(v/assert kb '(set/defaultRule (set/forwardRule
                (implies (republican ?x) (not (pacifist ?x))))) 'CxWell)
(v/assert kb '(set/forwardRule (implies (pacifist ?x) (opposes_war ?x))) 'CxWell)
(v/assert kb '(quaker Nixon)     'CxWell {:strength :monotonic})
(v/assert kb '(republican Nixon) 'CxWell {:strength :monotonic})

(v/ask? kb '(pacifist Nixon)       'CxWell)   ; => true
(v/ask? kb '(not (pacifist Nixon)) 'CxWell)   ; => true
(v/ask? kb '(opposes_war Nixon)    'CxWell)   ; => true — the dilemma's consequences fire
(count (v/contradictions kb))                 ; => 1
```

A dilemma's consequences propagate, and nothing marks a conclusion downstream of a
dilemma as tainted. The count of rules on each side does not matter: a third rule
concluding `pacifist` leaves the same dilemma, and defeasible logic agrees, since its
team defeat compares rules only through the superiority relation. The engine ranks two
`:default` sentences by nothing at all. Why it has no second axis:
[defenses.md](defenses.md#there-is-no-second-axis).

Three ways recover the skeptical answer:

- **Read the report.** `(v/contradictions kb)` names every standing dilemma with both
  sides' justifications. A caller that wants `−∂` on both sides withdraws the members
  itself.
- **Ask cautiously.** `(v/add-reasoner kb :brave-cautious)` and then
  `(v/ask? kb '(cautiously (pacifist Nixon)) 'CxWell)` returns `false`: the sentence holds
  in some resolution of the current dilemmas but not in every one. `(bravely …)` returns
  `true`. The read commits nothing → [labeling.md](labeling.md).
- **Write the tie as two exceptions.** When the theory says neither rule wins, give each
  rule the other's body as its exception. Neither fires, no dilemma forms, and nothing
  downstream fires. This form is ambiguity blocking for that pair:

  ```clojure
  (v/assert kb '(exceptWhen (republican ?x)
                  (set/defaultRule (set/forwardRule (implies (quaker ?x) (pacifist ?x)))))
            'CxWell)
  (v/assert kb '(exceptWhen (quaker ?x)
                  (set/defaultRule (set/forwardRule
                    (implies (republican ?x) (not (pacifist ?x))))))
            'CxWell)
  ;; (pacifist Nixon) and (not (pacifist Nixon)) are both unbelieved; contradictions is []
  ```

## Superiority compiles into `exceptWhen`

The engine has no `>`. The relation `r' > r` with `r'` concluding `¬p` and `r`
concluding `p` says that `r` does not conclude when `r'` is applicable. An
[`exceptWhen`](exceptions.md) on `r` whose query is `r'`'s body states the same thing:

```clojure
;; r : bird ⇒ flies        r' : broken_wing ⇒ ¬flies        r' > r
(v/assert kb '(exceptWhen (broken_wing ?x)
                (set/defaultRule (set/forwardRule (implies (bird ?x) (flies ?x)))))
          'CxWell)
(v/assert kb '(set/defaultRule (set/forwardRule (implies (broken_wing ?x) (not (flies ?x)))))
          'CxWell)
(v/assert kb '(bird Tweety)        'CxWell {:strength :monotonic})
(v/assert kb '(broken_wing Tweety) 'CxWell {:strength :monotonic})

(v/ask? kb '(not (flies Tweety)) 'CxWell)   ; => true
(v/ask? kb '(flies Tweety) 'CxWell)         ; => false, and no handle exists for it
(v/why-not kb '(flies Tweety) 'CxWell)      ; => {:reason :excepted :exception (broken_wing Tweety) …}
```

An excepted rule does not fire, so no `(flies Tweety)` is created and no contradiction
forms. `why-not` reports the argument the rule would have made and the exception that
stopped it.

**The general compilation.** For each rule `x` concluding `p`, and each rule `y`
concluding `¬p` where `x > y` does not hold, give `x` one exception:

- **Without team defeat**, the exception is `y`'s body.
- **With team defeat**, the exception is `y`'s body together with `(unknown <body of t>)`
  for every rule `t` concluding `p` with `t > y`. The rule `x` stands down only when no
  teammate beats `y`.

Repeat the construction with `p` and `¬p` swapped. A conjunction is a vector, and a rule
takes one `exceptWhen` per rival:

```clojure
;; x1: quaker ⇒ pacifist     y1: republican ⇒ ¬pacifist     x1 > y1
;; x2: churchgoer ⇒ pacifist y2: hawk ⇒ ¬pacifist           x2 > y2
(exceptWhen [(hawk ?x) (unknown (churchgoer ?x))] x1)      ; y2 beats x1 unless x2 is applicable
(exceptWhen [(republican ?x) (unknown (quaker ?x))] x2)    ; y1 beats x2 unless x1 is applicable
(exceptWhen (quaker ?x) y1)  (exceptWhen (churchgoer ?x) y1)
(exceptWhen (quaker ?x) y2)  (exceptWhen (churchgoer ?x) y2)
;; all four bodies hold for Nixon: (pacifist Nixon) is believed, as team defeat concludes
```

Without the `unknown` conjuncts, `x1` and `x2` each stand down and the same theory
concludes neither side, which is the individual-defeat reading.

Three limits apply to the compilation:

- **The exception must be closed by the rule's own antecedents.** A variable in `y`'s
  body that `x` does not bind is refused `:exception-not-closed`. A ground theory, the
  form SPINdle reasons over, always compiles. A theory with variables compiles only where
  the rivals share their variables.
- **Applicability is belief, read at level 6.** The exception holds when `y`'s body is
  believed in the conclusion's placement context, without backchaining. A body derived
  only by a backward rule does not count → [levels.md](levels.md).
- **A cycle through an exception is refused.** If a rival's body depends on `p` or
  `¬p`, the exception reads its own rule's conclusion, and the assert throws
  `:not-stratified` → [exceptions.md](exceptions.md#stratification).

## Defeaters

A defeater `heavy(X) ⇝ ¬flies(X)` blocks a conclusion and concludes nothing. Here it is
an exception with no rule for `¬flies` beside it:

```clojure
(v/assert kb '(exceptWhen (heavy ?x)
                (set/defaultRule (set/forwardRule (implies (bird ?x) (flies ?x)))))
          'CxWell)
(v/assert kb '(bird Dodo)  'CxWell {:strength :monotonic})
(v/assert kb '(heavy Dodo) 'CxWell {:strength :monotonic})

(v/ask? kb '(flies Dodo) 'CxWell)         ; => false
(v/ask? kb '(not (flies Dodo)) 'CxWell)   ; => false
```

A defeater in defeasible logic applies to every rule concluding `flies`. An `exceptWhen`
names one rule handle. A theory with several rules for `flies` therefore states the
exception on each one, and the superiority of a rule over a defeater means that rule
receives no exception. This is undercutting defeat: the exception removes the rule's
argument and asserts no rival → [exceptions.md](exceptions.md#semantics).

## The call you would have made

| in SPINdle | here |
|---|---|
| load a theory, then compute its conclusions | `assert` each sentence; belief is current after every `assert` |
| the conclusion set, `+∂` | `(v/query kb goal ctx)`, an ordinary read → [api.md](api.md) |
| `+Δ` against `+∂` for one literal | `(v/defeat-class kb handle)` |
| why a literal is `−∂` | `(v/why-not kb sentence ctx)` |
| the literals left unresolved by a tie | `(v/contradictions kb)` |
| skeptical consequence of the tie | `(cautiously S)` with the `:brave-cautious` reasoner |
| remove a rule and recompute | `(v/retract! kb (v/handle-of kb sentence ctx))`; what rested on it is withdrawn |

## What you keep

- Facts, strict rules and defeasible rules, with the same strength propagation from
  premises to conclusions
- Strict beating defeasible, and an inconsistent strict part left as it is
- Undercutting by defeaters, written as `exceptWhen`
- Order independence: the same theory asserted in any order reaches the same beliefs →
  [nmtms.md](nmtms.md#1-order-independence)

## What you lose

- The skeptical default. A tie between two defaults is believed on both sides and
  reported, unless the theory states the tie as two exceptions
- The superiority relation as a stored fact, and team defeat as a built-in. Both compile
  into `exceptWhen`, by hand
- Defeaters that apply to a literal rather than to one rule
- Modal defeasible logic: operator conversions, and conflicts between modalities such as
  an obligation against a prohibition. `believes`, `knows`, `desires` and `intends`
  project into agent contexts and stop there → [belief.md](belief.md)
- A reader for SPINdle's XML or text theory format

## What you gain

- First-order rules over individuals and types, without a grounding pass
- Contexts, so two theories that contradict each other coexist in one KB →
  [contexts.md](contexts.md)
- Incremental truth maintenance: an `assert` or a `retract!` relabels the region it
  touches, and `why` / `why-not` answer from the stored justifications
- Taxonomy closures for `genl` and `genlCx`, read by every match →
  [taxonomy.md](taxonomy.md)
- An opt-in answer set solve for a dilemma that has to be decided → [solving.md](solving.md)
