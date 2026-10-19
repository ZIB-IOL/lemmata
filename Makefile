.PHONY: check lean docs browser
check:   ; tools/check.sh
lean:    ; tools/check.sh --no-docs
browser: ; node tests/browser.mjs docs/_build/html ""
