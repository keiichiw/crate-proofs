use crc::{Algorithm,Crc,Table};
pub fn table_u8_l0(ctx:&Crc<u8,Table<0>>)->&[[u8;256];0]{ctx.table()}
pub fn clone_u8_l0(ctx:&Crc<u8,Table<0>>)->Crc<u8,Table<0>>{ctx.clone()}
pub fn full_u8_l0(alg:&'static Algorithm<u8>,data:&[u8],initial:u8)->u8{let crc=<Crc<u8,Table<0>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u8_l1(ctx:&Crc<u8,Table<1>>)->&[[u8;256];1]{ctx.table()}
pub fn clone_u8_l1(ctx:&Crc<u8,Table<1>>)->Crc<u8,Table<1>>{ctx.clone()}
pub fn full_u8_l1(alg:&'static Algorithm<u8>,data:&[u8],initial:u8)->u8{let crc=<Crc<u8,Table<1>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u8_l16(ctx:&Crc<u8,Table<16>>)->&[[u8;256];16]{ctx.table()}
pub fn clone_u8_l16(ctx:&Crc<u8,Table<16>>)->Crc<u8,Table<16>>{ctx.clone()}
pub fn full_u8_l16(alg:&'static Algorithm<u8>,data:&[u8],initial:u8)->u8{let crc=<Crc<u8,Table<16>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u16_l0(ctx:&Crc<u16,Table<0>>)->&[[u16;256];0]{ctx.table()}
pub fn clone_u16_l0(ctx:&Crc<u16,Table<0>>)->Crc<u16,Table<0>>{ctx.clone()}
pub fn full_u16_l0(alg:&'static Algorithm<u16>,data:&[u8],initial:u16)->u16{let crc=<Crc<u16,Table<0>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u16_l1(ctx:&Crc<u16,Table<1>>)->&[[u16;256];1]{ctx.table()}
pub fn clone_u16_l1(ctx:&Crc<u16,Table<1>>)->Crc<u16,Table<1>>{ctx.clone()}
pub fn full_u16_l1(alg:&'static Algorithm<u16>,data:&[u8],initial:u16)->u16{let crc=<Crc<u16,Table<1>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u16_l16(ctx:&Crc<u16,Table<16>>)->&[[u16;256];16]{ctx.table()}
pub fn clone_u16_l16(ctx:&Crc<u16,Table<16>>)->Crc<u16,Table<16>>{ctx.clone()}
pub fn full_u16_l16(alg:&'static Algorithm<u16>,data:&[u8],initial:u16)->u16{let crc=<Crc<u16,Table<16>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u32_l0(ctx:&Crc<u32,Table<0>>)->&[[u32;256];0]{ctx.table()}
pub fn clone_u32_l0(ctx:&Crc<u32,Table<0>>)->Crc<u32,Table<0>>{ctx.clone()}
pub fn full_u32_l0(alg:&'static Algorithm<u32>,data:&[u8],initial:u32)->u32{let crc=<Crc<u32,Table<0>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u32_l1(ctx:&Crc<u32,Table<1>>)->&[[u32;256];1]{ctx.table()}
pub fn clone_u32_l1(ctx:&Crc<u32,Table<1>>)->Crc<u32,Table<1>>{ctx.clone()}
pub fn full_u32_l1(alg:&'static Algorithm<u32>,data:&[u8],initial:u32)->u32{let crc=<Crc<u32,Table<1>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u32_l16(ctx:&Crc<u32,Table<16>>)->&[[u32;256];16]{ctx.table()}
pub fn clone_u32_l16(ctx:&Crc<u32,Table<16>>)->Crc<u32,Table<16>>{ctx.clone()}
pub fn full_u32_l16(alg:&'static Algorithm<u32>,data:&[u8],initial:u32)->u32{let crc=<Crc<u32,Table<16>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u64_l0(ctx:&Crc<u64,Table<0>>)->&[[u64;256];0]{ctx.table()}
pub fn clone_u64_l0(ctx:&Crc<u64,Table<0>>)->Crc<u64,Table<0>>{ctx.clone()}
pub fn full_u64_l0(alg:&'static Algorithm<u64>,data:&[u8],initial:u64)->u64{let crc=<Crc<u64,Table<0>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u64_l1(ctx:&Crc<u64,Table<1>>)->&[[u64;256];1]{ctx.table()}
pub fn clone_u64_l1(ctx:&Crc<u64,Table<1>>)->Crc<u64,Table<1>>{ctx.clone()}
pub fn full_u64_l1(alg:&'static Algorithm<u64>,data:&[u8],initial:u64)->u64{let crc=<Crc<u64,Table<1>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u64_l16(ctx:&Crc<u64,Table<16>>)->&[[u64;256];16]{ctx.table()}
pub fn clone_u64_l16(ctx:&Crc<u64,Table<16>>)->Crc<u64,Table<16>>{ctx.clone()}
pub fn full_u64_l16(alg:&'static Algorithm<u64>,data:&[u8],initial:u64)->u64{let crc=<Crc<u64,Table<16>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u128_l0(ctx:&Crc<u128,Table<0>>)->&[[u128;256];0]{ctx.table()}
pub fn clone_u128_l0(ctx:&Crc<u128,Table<0>>)->Crc<u128,Table<0>>{ctx.clone()}
pub fn full_u128_l0(alg:&'static Algorithm<u128>,data:&[u8],initial:u128)->u128{let crc=<Crc<u128,Table<0>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u128_l1(ctx:&Crc<u128,Table<1>>)->&[[u128;256];1]{ctx.table()}
pub fn clone_u128_l1(ctx:&Crc<u128,Table<1>>)->Crc<u128,Table<1>>{ctx.clone()}
pub fn full_u128_l1(alg:&'static Algorithm<u128>,data:&[u8],initial:u128)->u128{let crc=<Crc<u128,Table<1>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn table_u128_l16(ctx:&Crc<u128,Table<16>>)->&[[u128;256];16]{ctx.table()}
pub fn clone_u128_l16(ctx:&Crc<u128,Table<16>>)->Crc<u128,Table<16>>{ctx.clone()}
pub fn full_u128_l16(alg:&'static Algorithm<u128>,data:&[u8],initial:u128)->u128{let crc=<Crc<u128,Table<16>>>::new(alg);let mut d=crc.digest_with_initial(initial);d.update(data);let _=crc.digest().finalize();let _=crc.checksum(data);d.finalize()}
pub fn digest_clone_u8_l0<'a>(d:&crc::Digest<'a,u8,Table<0>>)->crc::Digest<'a,u8,Table<0>>{d.clone()}
pub fn digest_clone_u8_l1<'a>(d:&crc::Digest<'a,u8,Table<1>>)->crc::Digest<'a,u8,Table<1>>{d.clone()}
pub fn digest_clone_u8_l16<'a>(d:&crc::Digest<'a,u8,Table<16>>)->crc::Digest<'a,u8,Table<16>>{d.clone()}
pub fn digest_clone_u16_l0<'a>(d:&crc::Digest<'a,u16,Table<0>>)->crc::Digest<'a,u16,Table<0>>{d.clone()}
pub fn digest_clone_u16_l1<'a>(d:&crc::Digest<'a,u16,Table<1>>)->crc::Digest<'a,u16,Table<1>>{d.clone()}
pub fn digest_clone_u16_l16<'a>(d:&crc::Digest<'a,u16,Table<16>>)->crc::Digest<'a,u16,Table<16>>{d.clone()}
pub fn digest_clone_u32_l0<'a>(d:&crc::Digest<'a,u32,Table<0>>)->crc::Digest<'a,u32,Table<0>>{d.clone()}
pub fn digest_clone_u32_l1<'a>(d:&crc::Digest<'a,u32,Table<1>>)->crc::Digest<'a,u32,Table<1>>{d.clone()}
pub fn digest_clone_u32_l16<'a>(d:&crc::Digest<'a,u32,Table<16>>)->crc::Digest<'a,u32,Table<16>>{d.clone()}
pub fn digest_clone_u64_l0<'a>(d:&crc::Digest<'a,u64,Table<0>>)->crc::Digest<'a,u64,Table<0>>{d.clone()}
pub fn digest_clone_u64_l1<'a>(d:&crc::Digest<'a,u64,Table<1>>)->crc::Digest<'a,u64,Table<1>>{d.clone()}
pub fn digest_clone_u64_l16<'a>(d:&crc::Digest<'a,u64,Table<16>>)->crc::Digest<'a,u64,Table<16>>{d.clone()}
pub fn digest_clone_u128_l0<'a>(d:&crc::Digest<'a,u128,Table<0>>)->crc::Digest<'a,u128,Table<0>>{d.clone()}
pub fn digest_clone_u128_l1<'a>(d:&crc::Digest<'a,u128,Table<1>>)->crc::Digest<'a,u128,Table<1>>{d.clone()}
pub fn digest_clone_u128_l16<'a>(d:&crc::Digest<'a,u128,Table<16>>)->crc::Digest<'a,u128,Table<16>>{d.clone()}
pub fn table_clone_l0(t:&Table<0>)->Table<0>{t.clone()}
pub fn table_clone_l1(t:&Table<1>)->Table<1>{t.clone()}
pub fn table_clone_l16(t:&Table<16>)->Table<16>{t.clone()}
pub fn digest_clone_from_u8_l0<'a>(d:&mut crc::Digest<'a,u8,Table<0>>,s:&crc::Digest<'a,u8,Table<0>>){d.clone_from(s)}
pub fn digest_clone_from_u8_l1<'a>(d:&mut crc::Digest<'a,u8,Table<1>>,s:&crc::Digest<'a,u8,Table<1>>){d.clone_from(s)}
pub fn digest_clone_from_u8_l16<'a>(d:&mut crc::Digest<'a,u8,Table<16>>,s:&crc::Digest<'a,u8,Table<16>>){d.clone_from(s)}
pub fn digest_clone_from_u16_l0<'a>(d:&mut crc::Digest<'a,u16,Table<0>>,s:&crc::Digest<'a,u16,Table<0>>){d.clone_from(s)}
pub fn digest_clone_from_u16_l1<'a>(d:&mut crc::Digest<'a,u16,Table<1>>,s:&crc::Digest<'a,u16,Table<1>>){d.clone_from(s)}
pub fn digest_clone_from_u16_l16<'a>(d:&mut crc::Digest<'a,u16,Table<16>>,s:&crc::Digest<'a,u16,Table<16>>){d.clone_from(s)}
pub fn digest_clone_from_u32_l0<'a>(d:&mut crc::Digest<'a,u32,Table<0>>,s:&crc::Digest<'a,u32,Table<0>>){d.clone_from(s)}
pub fn digest_clone_from_u32_l1<'a>(d:&mut crc::Digest<'a,u32,Table<1>>,s:&crc::Digest<'a,u32,Table<1>>){d.clone_from(s)}
pub fn digest_clone_from_u32_l16<'a>(d:&mut crc::Digest<'a,u32,Table<16>>,s:&crc::Digest<'a,u32,Table<16>>){d.clone_from(s)}
pub fn digest_clone_from_u64_l0<'a>(d:&mut crc::Digest<'a,u64,Table<0>>,s:&crc::Digest<'a,u64,Table<0>>){d.clone_from(s)}
pub fn digest_clone_from_u64_l1<'a>(d:&mut crc::Digest<'a,u64,Table<1>>,s:&crc::Digest<'a,u64,Table<1>>){d.clone_from(s)}
pub fn digest_clone_from_u64_l16<'a>(d:&mut crc::Digest<'a,u64,Table<16>>,s:&crc::Digest<'a,u64,Table<16>>){d.clone_from(s)}
pub fn digest_clone_from_u128_l0<'a>(d:&mut crc::Digest<'a,u128,Table<0>>,s:&crc::Digest<'a,u128,Table<0>>){d.clone_from(s)}
pub fn digest_clone_from_u128_l1<'a>(d:&mut crc::Digest<'a,u128,Table<1>>,s:&crc::Digest<'a,u128,Table<1>>){d.clone_from(s)}
pub fn digest_clone_from_u128_l16<'a>(d:&mut crc::Digest<'a,u128,Table<16>>,s:&crc::Digest<'a,u128,Table<16>>){d.clone_from(s)}
pub fn table_clone_from_l0(d:&mut Table<0>,s:&Table<0>){d.clone_from(s)}
pub fn table_clone_from_l1(d:&mut Table<1>,s:&Table<1>){d.clone_from(s)}
pub fn table_clone_from_l16(d:&mut Table<16>,s:&Table<16>){d.clone_from(s)}
