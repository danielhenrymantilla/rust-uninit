.PHONY: test publish clean

test:
	cargo clean && cargo miri test --features nightly
	cargo clean && cargo test --features nightly
	cargo check --no-default-features --target thumbv6m-none-eabi

publish: test
	cargo publish --dry-run

clean:
	cargo clean

