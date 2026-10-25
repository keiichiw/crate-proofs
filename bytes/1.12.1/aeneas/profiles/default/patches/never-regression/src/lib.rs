#![no_std]
pub fn stop() -> ! { panic!("stop") }
pub fn guarded(n: u32) -> u32 { if n == 0 { stop() } n }
pub fn ordinary(n: u32) -> u32 { n }
#[allow(unconditional_recursion)]
pub fn diverge() -> ! { diverge() }
pub fn guarded_diverge(n: u32) -> u32 { if n == 0 { diverge() } n }
