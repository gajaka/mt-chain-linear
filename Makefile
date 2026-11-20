.PHONY: check migration core generic certificates windows biased provenance barrier

# Generic MT theory and the concrete chain have separate build scopes.
check: migration generic certificates windows biased provenance barrier

migration:
	python3 -B tooling/lean_migration.py
	python3 -B tooling/test_lean_migration.py

core:
	lake --wfail build

generic:
	cd library && lake --wfail build GenericMT
	python3 -B library/check.py

certificates: core
	cd research/certificate-existence && lake --wfail build CertificateStudy

windows:
	@set -e; for certificate in research/window-locality/evidence/*/CERTIFICATE.json; do \
		python3 -B research/window-locality/scripts/verify_certificate.py "$$certificate"; \
	done
	PYTHONOPTIMIZE=0 python3 -B research/window-locality/theory/homogeneous-width2/verify_raw_dual.py research/window-locality/theory/homogeneous-width2/DUAL_EXACT.json

biased: core
	cd research/biased-resampling && lake --wfail build BiasedResampling

provenance:
	python3 -B -c "import sys; sys.path.insert(0, 'scripts'); from provenance import validate_sources; print(validate_sources()['receipt'])"
	python3 -B research/certificate-existence/scripts/verify_sources.py

barrier:
	python3 -B experiments/barrier-guided-bias/verify.py
