use std::borrow::Cow;

fn chunks_fork(input: &[u8], size_hint_observations: &mut usize) -> Vec<String> {
    let mut fork_iter = fork::byte_serialize(input);
    let mut upstream_iter = upstream::byte_serialize(input);
    let mut chunks = Vec::new();
    loop {
        assert_eq!(fork_iter.size_hint(), upstream_iter.size_hint(), "size hint for {input:?}");
        *size_hint_observations += 1;
        match (fork_iter.next(), upstream_iter.next()) {
            (Some(left), Some(right)) => {
                assert_eq!(left, right, "serializer chunk for {input:?}");
                chunks.push(left.to_owned());
            }
            (None, None) => break,
            (left, right) => panic!("serializer termination differs for {input:?}: {left:?} vs {right:?}"),
        }
    }
    assert_eq!(fork_iter.size_hint(), upstream_iter.size_hint(), "terminal size hint for {input:?}");
    *size_hint_observations += 1;
    chunks
}

fn parse_fork(input: &[u8]) -> Vec<(String, String, bool, bool)> {
    fork::parse(input)
        .map(|(key, value)| {
            let key_borrowed = matches!(key, Cow::Borrowed(_));
            let value_borrowed = matches!(value, Cow::Borrowed(_));
            (key.into_owned(), value.into_owned(), key_borrowed, value_borrowed)
        })
        .collect()
}

fn parse_upstream(input: &[u8]) -> Vec<(String, String, bool, bool)> {
    upstream::parse(input)
        .map(|(key, value)| {
            let key_borrowed = matches!(key, Cow::Borrowed(_));
            let value_borrowed = matches!(value, Cow::Borrowed(_));
            (key.into_owned(), value.into_owned(), key_borrowed, value_borrowed)
        })
        .collect()
}

fn parse_owned(input: &[u8], use_fork: bool) -> Vec<(String, String)> {
    if use_fork {
        fork::parse(input).into_owned().collect()
    } else {
        upstream::parse(input).into_owned().collect()
    }
}

fn parse_clone_suffix(input: &[u8], use_fork: bool) -> (Vec<(String, String)>, Vec<(String, String)>) {
    if use_fork {
        let mut iter = fork::parse(input);
        let _consumed = iter.next();
        let cloned = iter.clone();
        (iter.map(|(k, v)| (k.into_owned(), v.into_owned())).collect(),
         cloned.map(|(k, v)| (k.into_owned(), v.into_owned())).collect())
    } else {
        let mut iter = upstream::parse(input);
        let _consumed = iter.next();
        let cloned = iter.clone();
        (iter.map(|(k, v)| (k.into_owned(), v.into_owned())).collect(),
         cloned.map(|(k, v)| (k.into_owned(), v.into_owned())).collect())
    }
}

#[derive(Default)]
struct ApiChecks {
    owned_parse_inputs: usize,
    clone_after_next_inputs: usize,
    size_hint_steps: usize,
}

fn check(input: &[u8], api: &mut ApiChecks) {
    let _chunks = chunks_fork(input, &mut api.size_hint_steps);
    assert_eq!(parse_fork(input), parse_upstream(input), "parser input {input:?}");
    assert_eq!(parse_owned(input, true), parse_owned(input, false), "owned parser input {input:?}");
    api.owned_parse_inputs += 1;
    assert_eq!(parse_clone_suffix(input, true), parse_clone_suffix(input, false), "cloned parser suffix {input:?}");
    api.clone_after_next_inputs += 1;
}

fn main() {
    let mut singleton_inputs = 0usize;
    let mut pair_inputs = 0usize;
    let mut alphabet_inputs = 0usize;
    let mut random_inputs = 0usize;
    let targeted_inputs: &[&[u8]] = &[
        b"%G1",
        b"%",
        b"%2",
        b"%2B",
        b"%252B",
        b"%C3%A9",
        b"%E2%82%AC",
        b"%F0%9F%92%A9",
        b"%C3%28",
        b"%E2%28%A1",
        b"%F0%28%8C%BC",
        b"%E2%82",
        b"%F0%9F%92",
    ];
    let mut api = ApiChecks::default();
    for input in targeted_inputs {
        check(input, &mut api);
    }
    for first in 0u8..=u8::MAX {
        check(&[first], &mut api);
        singleton_inputs += 1;
    }
    for first in 0u8..=u8::MAX {
        for second in 0u8..=u8::MAX {
            check(&[first, second], &mut api);
            pair_inputs += 1;
        }
    }

    fn enumerate(input: &mut Vec<u8>, alphabet: &[u8], remaining: usize, count: &mut usize, api: &mut ApiChecks) {
        if remaining == 0 {
            check(input, api);
            *count += 1;
            return;
        }
        for &byte in alphabet {
            input.push(byte);
            enumerate(input, alphabet, remaining - 1, count, api);
            input.pop();
        }
    }
    for length in 0..=5 {
        enumerate(&mut Vec::new(), b"&=+%0F\x80", length, &mut alphabet_inputs, &mut api);
    }

    let mut state = 0x9e37_79b9u32;
    for length in 0..=128 {
        let mut input = Vec::with_capacity(length);
        for _ in 0..length {
            state ^= state << 13;
            state ^= state >> 17;
            state ^= state << 5;
            input.push(state as u8);
        }
        check(&input, &mut api);
        random_inputs += 1;
    }

    let mut fork_target = String::from("prefix?");
    let fork_output = fork::Serializer::for_suffix(&mut fork_target, 7)
        .append_pair("a+b", "c d&%")
        .append_key_only("k=")
        .finish();
    let mut upstream_target = String::from("prefix?");
    let upstream_output = upstream::Serializer::for_suffix(&mut upstream_target, 7)
        .append_pair("a+b", "c d&%")
        .append_key_only("k=")
        .finish();
    assert_eq!(fork_output, upstream_output);

    let total = singleton_inputs + pair_inputs + alphabet_inputs + random_inputs;
    println!(
        "{{\"status\":\"passed\",\"singleton_inputs\":{singleton_inputs},\"pair_inputs\":{pair_inputs},\"alphabet_inputs\":{alphabet_inputs},\"random_inputs\":{random_inputs},\"targeted_escape_utf8_inputs\":{},\"byte_input_total\":{total},\"owned_parse_inputs\":{},\"clone_after_next_inputs\":{},\"size_hint_step_observations\":{},\"serializer_chain_cases\":1}}",
        targeted_inputs.len(), api.owned_parse_inputs, api.clone_after_next_inputs, api.size_hint_steps
    );
}
