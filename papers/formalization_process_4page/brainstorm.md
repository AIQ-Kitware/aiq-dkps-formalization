# Building Confidence in an LLM Formalization

Use the AI-assistant figure as the main figure. (from powerpoint)


### Outline

* Use Davis Kahan as the Case Study

* Ask how we can be Confident in The Process of LLM formalization?

* Show the LLM semantic alignment tool to help judge the correctness of the sine theta proof.

* Cite contemporaneous development of the finite DK sine theta.


### Informal Timeline Notes

Can I dump a pdf into GPT and get a formalization out?
Can we iterate without so many syntax errors?
WTF does this mean?
How do I trust this?
I don't understand why the AI is saying we can't do this.
I don't understand why the AI is proving something, saying its done, and then telling me it isn't the same thing as the paper.
At some point I start to understand the idea of missing foundational results, and learn to encourage the LLM to break the problem down and go after the smaller problems.
Tears and frustration.
Getting to the point where I could start to see the correspondence between lean and prose
Getting a subscription to the agentic models with a lean environment 

Spending a lot of tokens.

Worked on parts of parallelization in parallel with several agents.

Started to build tools to track the status of the formalization.

Started to ask agents for hostile reviews.

After a certain point, agents would stop finding items where it could say that
the semantic alignment was off. Having enough hostile reviews + a basic
understanding of lean + studying the relevant topic - often with the help of
LLMs = fairly high confidence in semantic alignment.


 

#### Relevant notes from emails:


If you can read the theorem statement and are 100% sure it aligns with your understanding of the theorem, and the proof compiles, then yes you can be sure that the conclusion is implied by the hypothesis, i.e. the proof is correct. You can use a #check statement to list out all of the axioms the proof depends on, which is how you check that sorry does not exist in the proof tree (sorry is an axiom that just says to accept the proof), but you could also go further e.g. by checking that your proof excludes classical choice if cared about constructive proofs.

The trick is being 100% sure that the theorem statement is exactly what you want, and I'm working on a tool to help put all of that information in front of a mathamatician right now. The idea is that it will also contain notes about the lean to help someone unfamiliar with it read it and make the connections.

I like this topic on math exchange about the issue: https://mathoverflow.net/a/513567 (I think some people on it are clutching pearls a bit, but there are some good points, especially about the excellent doohickeys versus quasi-excellent doohickeys).

One of the constant struggles I had while doing the DK proof is that an agent would say: "Oh yeah, we're done, we got the theorem 100% this is exactly right", and really it had only proven a special case of what I wanted. Granted I was being somewhat vauge, because I'm in the position where I don't really know exactly what I want, I just said: "proof Davis and Kahan's 1970 paper in full generality" without really understanding what that meant. So the agent might have gone on to prove a theorem in a finite case, or only for bounded operators, instead of the unbounded scope that is actually assumed throughout the original paper. I spent a lot of time putting the proof into fresh LLM sessions and asking it leading questions: "what is missing from this proof", or "find where this proof does not match what DK actually proved". For 2 months the agents would always find something, but now their ability to find any mismatch between the paper and the lean has dwindled, so I'm increasingly confident that what I have is correct. Still not 100% confident though.  


---


Yes, that is correct. You are trusting the kernel, and there have been soundness holes in it. 

There was actually a "proof" of a Collatz counterexample that passed the kernel due to a soundness bug: https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/

However, it's important to note that it wasn't a researcher trying to disprove Collatz and making a mistake. It was a person that was explicitly trying to exploit the kernel to make it accept the incorrect proof. So for all intents and purposes I don't worry about an LLM trying to sneak a proof through via a soundness hole.

This is similar to how other languages like rust with strong "proof" guarantees can also have soundness issues due to implementation bugs: https://github.com/Speykious/cve-rs

You end up running into Godel incompleteness and Rice's theorem when you try to use lean to prove lean is sound or prove that there isn't a bug in the implementation without making any assumptions. You could in theory use a different formal system to do formal verification of the lean kernel, but then you end up with a different trust surface. It's turtles all the way down (although with a sufficiently diverse and independent set of turtles, perhaps there is a statistical argument that can be made).


---

## Verbatim human prompt log for paper revision

This section is intended to preserve the human input that shaped the paper rather than a cleaned-up reconstruction of it. The entries below are copied verbatim from the retained drafting transcript available while preparing this overlay. The earlier brainstorming notes above predate this retained prompt log and remain in their original form. If an earlier chat export becomes available, prepend the missing prompts rather than paraphrasing them.

### Prompt 1

````text
We should make it focus on the sine theta theorem I think.
````

### Prompt 2

````text
  File "/home/joncrall/.local/uv/envs/uvpy3.13.13/lib/python3.13/site-packages/playwright/_impl/_connection.py", line 559, in wrap_api_call
    raise rewrite_error(error, f"{parsed_st['apiName']}: {error}") from None
playwright._impl._errors.TimeoutError: Locator.wait_for: Timeout 30000ms exceeded.
Call log:
  - waiting for locator("#S2-sin-theta") to be visible
````

### Prompt 3

````text
file:///home/joncrall/code/aiq-dkps-formalization/build/semantic-alignment/review.html#3-S2-sin-theta

Is what resolves in the brwoser, but (uvpy3.13.13) joncrall@toothbrush:~/code/aiq-dkps-formalization/papers/formalization_process_4page$ python render_semantic_dashboard.py 
src=PosixPath('/home/joncrall/code/aiq-dkps-formalization/build/semantic-alignment/review.html')
Traceback (most recent call last):
  File "/home/joncrall/code/aiq-dkps-formalization/papers/formalization_process_4page/render_semantic_dashboard.py", line 64, in <module>
    row.wait_for(state='visible')
    ~~~~~~~~~~~~^^^^^^^^^^^^^^^^^
  File "/home/joncrall/.local/uv/envs/uvpy3.13.13/lib/python3.13/site-packages/playwright/sync_api/_generated.py", line 18670, in wait_for
    self._sync(self._impl_obj.wait_for(timeout=timeout, state=state))
    ~~~~~~~~~~^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  File "/home/joncrall/.local/uv/envs/uvpy3.13.13/lib/python3.13/site-packages/playwright/_impl/_sync_base.py", line 115, in _sync
    return task.result()
           ~~~~~~~~~~~^^
  File "/home/joncrall/.local/uv/envs/uvpy3.13.13/lib/python3.13/site-packages/playwright/_impl/_locator.py", line 723, in wait_for
    await self._frame.wait_for_selector(
        self._selector, strict=True, timeout=timeout, state=state
    )
  File "/home/joncrall/.local/uv/envs/uvpy3.13.13/lib/python3.13/site-packages/playwright/_impl/_frame.py", line 369, in wait_for_selector
    await self._channel.send(
        "waitForSelector", self._timeout, locals_to_params(locals())
    )
  File "/home/joncrall/.local/uv/envs/uvpy3.13.13/lib/python3.13/site-packages/playwright/_impl/_connection.py", line 69, in send
    return await self._connection.wrap_api_call(
           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    ...<3 lines>...
    )
    ^
  File "/home/joncrall/.local/uv/envs/uvpy3.13.13/lib/python3.13/site-packages/playwright/_impl/_connection.py", line 559, in wrap_api_call
    raise rewrite_error(error, f"{parsed_st['apiName']}: {error}") from None
playwright._impl._errors.Error: Locator.wait_for: SyntaxError: Failed to execute 'querySelectorAll' on 'Document': '#3-S2-sin-theta' is not a valid selector.
    at query (<anonymous>:5261:41)
    at <anonymous>:5271:7
    at SelectorEvaluatorImpl._cached (<anonymous>:5048:20)
    at SelectorEvaluatorImpl._queryCSS (<anonymous>:5258:17)
    at SelectorEvaluatorImpl._querySimple (<anonymous>:5138:19)
    at <anonymous>:5086:29
    at SelectorEvaluatorImpl._cached (<anonymous>:5048:20)
    at SelectorEvaluatorImpl.query (<anonymous>:5079:19)
    at Object.query (<anonymous>:5293:44)
    at <anonymous>:5251:21
Call log:
  - waiting for locator("#3-S2-sin-theta") to be visible

in #!/usr/bin/env python3
import pathlib
import shutil
import subprocess

from playwright.sync_api import sync_playwright


repo = pathlib.Path(
    subprocess.check_output(
        ['git', 'rev-parse', '--show-toplevel'],
        text=True,
    ).strip()
)

src = repo / 'build/semantic-alignment/review.html'
out_dpath = repo / 'papers/formalization_process_4page/figures'
out_dpath.mkdir(parents=True, exist_ok=True)

if not src.exists():
    raise FileNotFoundError(
        f'Semantic-alignment page does not exist: {src}\n'
        'Run ./semantic-alignment-page.sh from the repository root first.'
    )

browser_exe = (
    shutil.which('google-chrome')
    or shutil.which('google-chrome-stable')
    or shutil.which('chromium')
    or shutil.which('chromium-browser')
)

if browser_exe is None:
    raise RuntimeError('Could not find Chrome or Chromium')

print(f'{src=}')
url = src.resolve().as_uri() + '#3-S2-sin-theta'

with sync_playwright() as p:
    browser = p.chromium.launch(
        headless=True,
        executable_path=browser_exe,
    )

    context = browser.new_context(
        viewport={'width': 2600, 'height': 1500},
        device_scale_factor=2,
    )

    page = context.new_page()
    page.goto(url, wait_until='networkidle')

    page.evaluate(
        '''
        async () => {
            if (document.fonts && document.fonts.ready) {
                await document.fonts.ready;
            }
        }
        '''
    )

    row = page.locator('#3-S2-sin-theta')
    row.wait_for(state='visible')

    page.screenshot(
        path=str(out_dpath / 'semantic-alignment-sine-theta-dashboard.png'),
        full_page=False,
    )

    row.screenshot(
        path=str(out_dpath / 'semantic-alignment-sine-theta-row.png'),
    )

    browser.close()

print(f'Wrote screenshots to: {out_dpath}')
````

### Prompt 4

````text
Use file:///home/joncrall/code/aiq-dkps-formalization/papers/formalization_process_4page/figures/semantic-alignment-sine-theta-row.png and give me the updated paper that uses this figure.
````

### Prompt 5

````text
We need both figures in the paper, we can cut off part of the bottom of the screenshot if we need to. DO NOT USE YOUR IMAGE GENERATOR. Add them as includegraphics. Your image generator classifier is so bad. Gain some space by getting rid of LLMisms, and LLM tics.
````

### Prompt 6

````text
We still have a huge amount of space left on page 4. And Table 1 isn't formated very well, and probably is not helping. I want numbered refs not names. Make sure we cite and talk about TauCeti given that its in the figure.
````

### Prompt 7

[The assistant had just delivered the v6 overlay.]

````text
unzip command
````

### Prompt 8

````text
honestly this paper is a huge slop pile.
````

### Prompt 9

````text
no no I don't think you're getting it. it's incredibly obvious that it's written by an LLM. and the wording I can fix that's not a problem, the problem is the content. your lessons are all things that an llm wants. a human's not going to check the elaboration. especially not one who barely knows lean. they're using an llm to do that for you and frankly all the lessons are things that llms do anyway. you just regurgitating your biases.
````

### Prompt 10

````text
I'm wondering if there are other sources online were people have discussed this topic. places where people have talked about real human experience with doing this. places that we can fight even if it's not a formal paper, but this paper can become a place to collect those observations and anecdotes.
````

### Prompt 11

[The assistant had returned an initial set of first-person reports and recurring observations.]

````text
search for more patterns to build a bigger corpus
````

### Prompt 12

````text
write the overlay that creates the coded corpus document and update the paper to consume it and make an interesting workshop paper.
````

### Prompt 13

[The assistant had described the source collection using the user's borrowed terms "corpus" and "survey" too strongly.]

````text
you're doing the thing where you're saying something is something but not something else again. it's a snapshot not a survey. cut it out. also calling a small coded corpus is not how anyone would really describe it. just because I mirror a term that you're using doesn't mean it's a good term. I do wonder if we can make a compelling measurement of the explosion and lean formalization. and maybe point out the time where this one started. it is worth a very brief and concise mention to say to all the data associated with this public. we will likely do a git in the abstract or somewhere in the paper where it makes sense.
````

### Prompt 14

[The assistant had produced a version titled "Who Checks the Formalization? Human Supervision in LLM-Assisted Lean" and still claimed 29/29 too strongly.]

````text
Oh, that title sucks. Not modest. Not cute. Let's add this to the story. Let's say we don't know if we really have all 29/29 Davis Kahan proofs at a source faithful level. We think we do, and if not we are very close. Let's instead of Figure 2, do something like the first section of the draft2 paper, where we give a lean formalization in the tex itself, and compare it to the prose. But let's do an example where there is a subtle misalignment based on a real error we have had in the past. Also add to the brainstorm document a list of every prompt I've typed verbatim (if it needs context from your words, insert a small summary of what I'm responding to, but keep it concise, the goal is to maintain a list of what the human actually had to type to get this paper right, it's my actual input to the paper).
````

### Prompt 15

[User-provided agent handoff; wording authored by another agent.]

````text
I have a summary of discussion with another agent, not sure how important it is. They are not my words though: Handoff: post-pivot findings
The paper direction changed after we realized the earlier “lessons” were largely LLM-centric prescriptions rather than observations about how humans actually work with LLM-assisted formalization.

### 1. New framing: collect human experience, do not invent best practices

The more interesting paper may be an **experience report plus synthesis of practitioner reports**. There is now a sizable scattered corpus of mathematicians/researchers describing what actually happened when they used LLMs to formalize mathematics.

Important recurring sources found after the pivot:

- Thomas Kahle — formalizing his own older paper with Claude Code.
- Thomas Nowak / Matthias Függer — Codex producer + Claude reviewer; extra hypotheses found after compilation.
- Jukka Suomela — deliberately does not read generated Lean; uses Lean as verification backend mediated by LLMs.
- Ilya Sergey — human intervention mainly at representation, decomposition, and missing-lemma level.
- Terence Tao / Sendov transcript — repeated plan restatement catches drift; human steering is conceptual/architectural.
- Haruhisa Enomoto — formalization found a false intermediate claim missed by informal AI review; later “proof digestion” as a separate human activity.
- Brett Saiki — altered definitions / extra hypotheses / agent thrashing / supervision fatigue.
- Boris Alexeev / Xena Erdős work — many concrete misformalizations: wrong variables, hypotheses, inequalities, quantifiers, etc.
- Vasily Ilin — hypothesis creep, definition-alignment bugs, agent avoidance behavior.
- Armstrong/Kuusi — explicit paper↔Lean correspondence documents and cases where Lean result is intentionally narrower.
- ZK Security FRI work — Claude decomposes/conjectures, Aristotle proves or counterexamples them.
- Sang-il Oum — formalization exposed a missing hypothesis in the source paper.
- Timothy Gowers — successful AI-assisted formalization without knowing Lean.
- Collins et al. — actual human-subject study of human–AI formalization workflows.

The striking recurring patterns are:

- There is **no consensus that a human must read Lean**.
- Statement/definition mismatch is repeatedly the main semantic failure mode.
- Multiple-agent role separation emerges independently: producer/reviewer, planner/prover, prover/back-translator.
- Human intervention is often conceptual: theorem scope, decomposition, representations, missing lemmas, deciding when the agent is stuck.
- Agents often fail by persisting in a bad direction rather than cleanly stopping.
- Counterexamples are a particularly useful channel for communicating formalization problems back to humans.
- Formalization frequently changes/corrects the informal mathematics.
- Human understanding can come **after** formal verification (“proof digestion”).
- Large projects independently invent persistent external state because chat history is inadequate.
- Missing foundations turn paper formalization into library development.
- AI-generated Lean volume is growing faster than humans can audit line-by-line.
- Workflows become obsolete over periods of months as models/tools improve.

The paper should probably **code these observations rather than declare universal lessons**. Preserve exact source passages and distinguish practitioner reports from empirical studies.

### 2. Related-work/tool pivot: what should we actually use?

User has not read the related-work systems yet and wants to understand them before submission, especially open/free tools that could improve the current Davis–Kahan semantic audit.

Key conclusion: **there is no obvious existing tool that replaces the current dashboard end-to-end**. The relevant ecosystem solves different pieces.

Most relevant tools:

- **Lean Atlas / Lean Compass** — MIT, local/open. Computes the subset of declarations whose semantics can affect a target theorem, pruning proof-only dependencies. Very relevant.
- **EconCSLib** — Apache-2.0, open. Closest conceptual peer to the current paper-facing semantic dashboard: source text, Lean statements, human review, ledgers/provenance. Study closely, but its machinery seems embedded in its own project rather than packaged as a generic auditor.
- **BEq+ / LeanInteract** — MIT/open. Given two *formal Lean statements*, tries to establish equivalence in both directions. Potentially very useful for selected correspondence claims where a clean formal reference theorem can be written.
- **ShadowBench / SA-Pass** — characterizes target semantics with auxiliary “shadow statements” and checks implications both ways. Conceptually very relevant to our clause decomposition. Public paper is extremely recent; no obvious reusable implementation was found yet.
- **CriticLean** — Apache-2.0 with open critic checkpoints. Possible extra independent semantic critic; less urgent than deterministic/formal audit tools.
- **LeanArchitect** — open blueprint/informal↔formal maintenance; useful infrastructure, not primarily semantic equivalence checking.
- **LeanMarathon / AutoformBot / FormaTheoria** — worth reading for workflow design, but too heavy or insufficiently packaged to adopt merely to audit the current DK repository.

### 3. Important refinement: the graph is not the real need

User clarified that they **already have a graph view**, and graph visualization is not important.

The real audit problem is:

> Given one theorem statement, expose every structure, predicate, abbreviation, typeclass, coercion, and project definition that contributes to what that theorem means, so a human can understand the semantic vocabulary of the theorem.

The current dashboard is weak here. It shows the elaborated theorem but does not make structure definitions easy to inspect.

This makes **Lean Compass** particularly interesting as a backend concept, because it distinguishes semantic/type-level dependencies from irrelevant proof dependencies.

But Compass reportedly treats Mathlib as a trusted base. That is fine for proof trust, but **not sufficient for comprehension**. For semantic alignment with Davis–Kahan, the human may still need to understand what Mathlib's `SelfAdjoint`, `ContinuousLinearMap`, `RCLike`, norm structures, etc. actually mean.

### 4. “Semantic vocabulary inspector” is likely the missing capability

The desired theorem-centric UI should make meaningful names in the elaborated theorem clickable.

For a project structure such as `SymmetricNormingFunction`, show:

- exact source declaration;
- kind (`structure`, definition, class, abbreviation, predicate);
- fields;
- parent structures/classes;
- mathematical/docstring explanation;
- source location;
- how it appears in this theorem;
- recursively expandable semantic dependencies.

For Mathlib structures, do the same against the **exact pinned Mathlib revision**.

Layer it instead of recursively dumping everything:

1. theorem statement;
2. immediate semantic vocabulary;
3. project-defined vocabulary — probably open by default;
4. Mathlib mathematical vocabulary — collapsed but expandable;
5. foundational Lean/kernel machinery — normally hidden.

Important distinction borrowed from Compass:

> Do not show everything the proof depends on. Show the declarations required to **interpret the theorem statement**.

This is much closer to the user's original goal: give a mathematician who may barely know Lean enough information to understand what the formal theorem is actually saying.

### 5. LeanExplore may provide useful implementation ideas

LeanExplore became more relevant once the requirement was clarified.

Potentially useful pieces:

- extracts declarations, types, source, and dependencies;
- groups compiler-generated declarations back into the original user-authored `structure`/`inductive` declaration (“StatementGroup”-like behavior);
- has local/self-hostable components;
- generates informal descriptions from declaration context.

Do **not** treat a hosted LeanExplore index as authoritative for an audit unless it exactly matches the project's pinned environment. Use the project's own Lean environment/source as ground truth. LeanExplore is more useful as an implementation/UI reference.

### 6. Likely next technical experiment

For the current DK repository:

1. Run **Lean Compass** on `S2-sin-theta` and perhaps a few other headline results.
2. Compare its semantic review cone with the existing dashboard's “statement closure.”
3. Inspect disagreements.
4. Add a **Definition / Structure Inspector** to the existing Lean pane using exact local Lean declarations.
5. Make all semantically meaningful names in the theorem clickable.
6. Include Mathlib definitions for comprehension even if Mathlib is trusted for proof correctness.
7. Later experiment with BEq+ for selected formal correspondences and ShadowBench-style obligations for clause-level claims.

Do not spend effort replacing the existing graph view.

### 7. Implication for the paper

The “what we would do differently next time” section should stop saying generic things like “inspect elaborated statements.”

A better concrete observation is:

> We would begin with existing semantic-audit tools, particularly tools that reduce the theorem to the definitions whose meanings must be understood, and we would give the human a way to inspect those definitions without requiring them to become fluent Lean readers.

The current dashboard remains useful because it connects **source text → correspondence claims → Lean artifact**, but it should be presented candidly as incomplete: its biggest weakness is currently exposing the meaning of the structures used by the Lean statement.
````

### Prompt 16

````text
I love the new name. I want to include the line in the paper: And the honest answer at this point is: I don't know, probably. If not, it's pretty close.  We should probably include some statistical argument. I would love to reference excellent doohickeys and quasi excellent doohickeys (with a citation). 

I want to be sure our data is high quality structured and easy for someone else to corroborate it. We don't want to talk much about the internal chatter of the LLMs. The entire a correspondence was reopened. Like details of the cencus. We just talk about it from a basic tooling level. We also briefly mention our tooling leanq with a github link, and also talk about related lean helper tools that help agents with lean. I think we mention that we found that one of the statements in the Davis Kahan paper is false as a brief line. That is interesting and worth a mention. WE NEVER USE THE WORDS: worth a mention or similar. 

I like the how much lean to humans have to read part.

This line:

> The first time
>
> was informative; the later reopenings were more informative. A terminal status is useful
>
> for project management, while confidence in source correspondence accumulates from the
>
> evidence behind that status:

Is very LLM-y in a sloppy way, I don't like it. The discussion of the LLM drafting the paper is good.

Let's include a hash of materials in the appendix. We can put a screenshot of our tool in the appendix.

We need to makes ure we are using good lean highlighting, the draft2 paper shows how to do it correctly. 

We have to introduce some intuitive way to think about Davis Kahan or the sine 2theta problem. We can't just use math and not say what it is. 

We an include a glossary in the appendix too. 

Add Brian Hu as an author. A timeline figure, if we have real data for it would also be useful, probably with tikz. That might be an appendix sort of thing. 

We should have an appendix that gives the cost of the formalization, taken mostly from draft2, I don't want to make a big deal of it here though. Not a contribution. Just transparency. Need the DARPA acknowledgment too. 
````
