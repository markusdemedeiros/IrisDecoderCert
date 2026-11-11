.PHONY: check theorem

# The project checker applies memory limits to each Lean invocation itself.
check:
	python3 tools/check-project

# Fast recheck of the public theorem using the existing dependency cache.
theorem:
	tools/bounded-build --small tools/check-iris SbrClient/Client/VerifiedReadyService.lean
