// Independent bit-level, width-local polynomial recurrence. No upstream utilities/tables.
use crc::*;
fn mask(width: u8) -> u128 { u128::MAX >> (128-width) }
fn reverse(mut x: u128, width: u8) -> u128 {
    let mut y=0; for _ in 0..width { y=(y<<1)|(x&1); x>>=1; } y
}
fn oracle(width:u8, poly:u128, initial:u128, refin:bool, refout:bool, xorout:u128, data:&[u8])->u128 {
    let m=mask(width); let mut r=initial&m;
    for &byte in data { for i in 0..8 {
        let bit=if refin {(byte>>i)&1} else {(byte>>(7-i))&1};
        let feedback=((r>>(width-1))&1) ^ u128::from(bit);
        r=(r<<1)&m; if feedback!=0 {r^=poly;}
    }}
    (if refout {reverse(r,width)} else {r}) ^ xorout
}
macro_rules! suite {
 ($name:ident,$ty:ty,$catalog:expr) => {
 #[test] fn $name() {
    let catalog: &[Algorithm<$ty>] = $catalog;
    let mut algorithms: Vec<Algorithm<$ty>>=catalog.to_vec();
    for width in 1..=<$ty>::BITS as u8 { for flags in 0..4 { for seed in [0u128,1,0x9e3779b97f4a7c15,u128::MAX] {
        let m=mask(width);
        algorithms.push(Algorithm {width,poly:((seed|1)&m) as $ty,init:(seed&m) as $ty,
          refin:flags&1!=0,refout:flags&2!=0,xorout:((seed.rotate_left(19))&m) as $ty,check:0,residue:0});
    }}}
    let mut bytes=[0u8;257]; let mut state=0x123456789abcdef0u64;
    for b in &mut bytes {state^=state<<13;state^=state>>7;state^=state<<17;*b=state as u8;}
    for (index,algorithm) in algorithms.into_iter().enumerate() {
        let alg: &'static Algorithm<$ty>=Box::leak(Box::new(algorithm));
        if index<catalog.len() { assert_eq!(oracle(alg.width,alg.poly as u128,alg.init as u128,alg.refin,alg.refout,alg.xorout as u128,b"123456789"),alg.check as u128); }
        macro_rules! lane { ($lane:literal) => {{
          let crc=Crc::<$ty,Table<$lane>>::new(alg); let mut copy=crc.clone(); copy.clone_from(&crc);
          assert!(std::ptr::eq(crc.algorithm,alg)); assert_eq!(crc.table().len(),$lane);
          assert_eq!(crc.table(),copy.table());
          for (lane,row) in crc.table().iter().enumerate() { for entry in [0,1,2,127,128,255] {
             let mut input=[0u8;16]; input[0]=entry as u8;
             let value=oracle(alg.width,alg.poly as u128,0,alg.refin,alg.refin,0,&input[..lane+1]);
             let aligned=if alg.refin {value} else {value << (<$ty>::BITS as u8-alg.width)};
             assert_eq!(row[entry],aligned as $ty,"table width={} lane={} entry={}",alg.width,lane,entry);
          }}
          for length in [0,1,2,7,8,15,16,17,31,32,33,63,64,65,127,128,129,255,256,257] {
            let data=&bytes[..length];
            let expected=oracle(alg.width,alg.poly as u128,alg.init as u128,alg.refin,alg.refout,alg.xorout as u128,data) as $ty;
            assert_eq!(crc.checksum(data),expected,"width={} lane={} flags={}/{} len={}",alg.width,$lane,alg.refin,alg.refout,length);
            let mut d=crc.digest(); d.update(&[]); let split=length/2; d.update(&data[..split]);
            let mut cloned=d.clone(); cloned.clone_from(&d); d.update(&data[split..]); cloned.update(&data[split..]);
            assert_eq!(d.finalize(),expected); assert_eq!(cloned.finalize(),expected);
            for initial in [0,mask(alg.width) as $ty,alg.init,<$ty>::MAX] {
               let want=oracle(alg.width,alg.poly as u128,initial as u128,alg.refin,alg.refout,alg.xorout as u128,data) as $ty;
               let mut custom=crc.digest_with_initial(initial); for chunk in data.chunks(7) {custom.update(chunk);} assert_eq!(custom.finalize(),want);
            }
          }
        }}; }
        lane!(0);lane!(1);lane!(16);
    }
 }
 };
}
#[test] fn table_clone_and_copy() {
  fn check<const L:usize>() {let t=Table::<L>{}; let copy=t; let mut cloned=copy.clone(); cloned.clone_from(&t); let _again=t;}
  check::<0>();check::<1>();check::<16>();
}

suite!(width_8,u8,&[CRC_3_GSM,CRC_3_ROHC,CRC_4_G_704,CRC_4_INTERLAKEN,CRC_5_EPC_C1G2,CRC_5_G_704,CRC_5_USB,CRC_6_CDMA2000_A,CRC_6_CDMA2000_B,CRC_6_DARC,CRC_6_G_704,CRC_6_GSM,CRC_7_MMC,CRC_7_ROHC,CRC_7_UMTS,CRC_8_AUTOSAR,CRC_8_BLUETOOTH,CRC_8_CDMA2000,CRC_8_DARC,CRC_8_DVB_S2,CRC_8_GSM_A,CRC_8_GSM_B,CRC_8_HITAG,CRC_8_I_432_1,CRC_8_I_CODE,CRC_8_LTE,CRC_8_MAXIM_DOW,CRC_8_MIFARE_MAD,CRC_8_NRSC_5,CRC_8_OPENSAFETY,CRC_8_ROHC,CRC_8_SAE_J1850,CRC_8_SMBUS,CRC_8_TECH_3250,CRC_8_WCDMA]);

suite!(width_16,u16,&[CRC_10_ATM,CRC_10_CDMA2000,CRC_10_GSM,CRC_11_FLEXRAY,CRC_11_UMTS,CRC_12_CDMA2000,CRC_12_DECT,CRC_12_GSM,CRC_12_UMTS,CRC_13_BBC,CRC_14_DARC,CRC_14_GSM,CRC_15_CAN,CRC_15_MPT1327,CRC_16_ARC,CRC_16_CDMA2000,CRC_16_CMS,CRC_16_DDS_110,CRC_16_DECT_R,CRC_16_DECT_X,CRC_16_DNP,CRC_16_EN_13757,CRC_16_GENIBUS,CRC_16_GSM,CRC_16_IBM_3740,CRC_16_IBM_SDLC,CRC_16_ISO_IEC_14443_3_A,CRC_16_KERMIT,CRC_16_LJ1200,CRC_16_M17,CRC_16_MAXIM_DOW,CRC_16_MCRF4XX,CRC_16_MODBUS,CRC_16_NRSC_5,CRC_16_OPENSAFETY_A,CRC_16_OPENSAFETY_B,CRC_16_PROFIBUS,CRC_16_RIELLO,CRC_16_SPI_FUJITSU,CRC_16_T10_DIF,CRC_16_TELEDISK,CRC_16_TMS37157,CRC_16_UMTS,CRC_16_USB,CRC_16_XMODEM]);

suite!(width_32,u32,&[CRC_17_CAN_FD,CRC_21_CAN_FD,CRC_24_BLE,CRC_24_FLEXRAY_A,CRC_24_FLEXRAY_B,CRC_24_INTERLAKEN,CRC_24_LTE_A,CRC_24_LTE_B,CRC_24_OPENPGP,CRC_24_OS_9,CRC_30_CDMA,CRC_31_PHILIPS,CRC_32_AIXM,CRC_32_AUTOSAR,CRC_32_BASE91_D,CRC_32_BZIP2,CRC_32_CD_ROM_EDC,CRC_32_CKSUM,CRC_32_ISCSI,CRC_32_ISO_HDLC,CRC_32_JAMCRC,CRC_32_MEF,CRC_32_MPEG_2,CRC_32_XFER]);

suite!(width_64,u64,&[CRC_40_GSM,CRC_64_ECMA_182,CRC_64_GO_ISO,CRC_64_MS,CRC_64_NVME,CRC_64_REDIS,CRC_64_WE,CRC_64_XZ]);

suite!(width_128,u128,&[CRC_82_DARC]);

include!("native-mutation.rs");
