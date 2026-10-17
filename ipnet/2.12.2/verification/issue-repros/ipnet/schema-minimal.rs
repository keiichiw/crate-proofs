use ipnet::{IpNet, Ipv6Net};
use serde_json::json;

fn main() {
    let net: IpNet = "0.0.0.0/0".parse().unwrap();
    let invalid = "a/64";
    assert!(serde_json::from_value::<Ipv6Net>(json!(invalid)).is_err());
    println!("{}", json!({
        "valid_value": serde_json::to_value(net).unwrap(),
        "invalid_value": invalid,
        "v08": {"net": schemars08::schema_for!(IpNet),
                "v6": schemars08::schema_for!(Ipv6Net)},
        "v1": {"net": schemars1::schema_for!(IpNet),
               "v6": schemars1::schema_for!(Ipv6Net)}
    }));
}
