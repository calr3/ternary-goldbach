# Notes for Claude

## Working preferences

* Commit straight to `main` and push there. Don't create branches; they confuse people.
* Whenever you draft a message for the Lean Zulip (the "Formalization of Ternary Goldbach" topic in
  #Autoformalization), give it as copyable plain text in Zulip's Markdown, inside a fenced code
  block, so that it can be pasted as is. Use a longer fence (```` or more) if the message itself
  contains ```. Don't post it yourself unless asked.
* The draft is only the robot-written part, in the thread's convention (see Helfgott's "Hi
  hoomans" post of 2026-11-16): all of Claude's text goes inside a spoiler block, and the message
  must include the robot emoji, so put it in the spoiler's title. Charlie writes the human part
  around it. For example:

  ````
  ```spoiler :robot: Claude's summary
  - …
  ```
  ````

  Inside the spoiler, write names as plain text ("@Steve Hubbard", no `**`), as Helfgott's robot
  summaries do; real @-mentions, which notify, go in Charlie's wrapping.

## Zulip Markdown

* Mentions: `@**Full Name|user_id**` (a silent mention is `@_**Full Name|user_id**`). Known IDs:
  Harald Helfgott 603502, Steve Hubbard 1235693, Charlie Reams 1224567.
* Inline code in backticks; links as `[text](url)` or plain URLs; math as `$$...$$`.
* Quotes: a ```` ```quote ```` block; collapsible text: a ```` ```spoiler Title ```` block.
* Link to the thread with `#**Autoformalization>Formalization of Ternary Goldbach**`.
