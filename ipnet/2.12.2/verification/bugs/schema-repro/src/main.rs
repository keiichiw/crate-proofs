use ipnet::{IpNet, Ipv4Net, Ipv6Net};
use serde_json::json;

fn main() {
    let samples = ["192.168.0.0/24", "0.0.0.0/0", "fd00::/32", "a/64"];
    let values: Vec<_> = samples
        .iter()
        .map(|s| {
            let parsed = s.parse::<IpNet>();
            json!({"input": s, "ipnet_parses": parsed.is_ok(),
            "ipv6_parses": s.parse::<Ipv6Net>().is_ok(),
            "ipnet_deserializes": serde_json::from_value::<IpNet>(json!(s)).is_ok(),
            "ipv6_deserializes": serde_json::from_value::<Ipv6Net>(json!(s)).is_ok(),
            "serialized": parsed.ok().map(|n| serde_json::to_value(n).unwrap())})
        })
        .collect();
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schemars08": {
                "IpNet": schemars08::schema_for!(IpNet),
                "Ipv4Net": schemars08::schema_for!(Ipv4Net),
                "Ipv6Net": schemars08::schema_for!(Ipv6Net)
            },
            "schemars1": {
                "IpNet": schemars1::schema_for!(IpNet),
                "Ipv4Net": schemars1::schema_for!(Ipv4Net),
                "Ipv6Net": schemars1::schema_for!(Ipv6Net)
            },
            "samples": values
        }))
        .unwrap()
    );
}
