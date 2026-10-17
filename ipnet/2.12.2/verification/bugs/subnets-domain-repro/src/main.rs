use ipnet::Ipv4Subnets;
use std::net::Ipv4Addr;
fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    for (start, end, q) in [
        (Ipv4Addr::UNSPECIFIED, Ipv4Addr::UNSPECIFIED, 33u8),
        (Ipv4Addr::UNSPECIFIED, Ipv4Addr::UNSPECIFIED, 255u8),
        (Ipv4Addr::new(0,0,0,1), Ipv4Addr::UNSPECIFIED, 33u8),
        (Ipv4Addr::UNSPECIFIED, Ipv4Addr::UNSPECIFIED, 32u8),
    ] {
        let result = std::panic::catch_unwind(|| Ipv4Subnets::new(start, end, q).next());
        match result {
            Ok(v) => println!("{start}..={end} q={q}: Ok({v:?})"),
            Err(e) => {
                let message = e.downcast_ref::<String>().map(String::as_str)
                    .or_else(|| e.downcast_ref::<&str>().copied()).unwrap_or("non-string panic");
                println!("{start}..={end} q={q}: panic({message})");
            }
        }
    }
}
