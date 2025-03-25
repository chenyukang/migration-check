#[test]
fn test_bin_serde() {
    #[derive(serde::Serialize, serde::Deserialize, Debug)]
    struct TestStruct {
        a: u8,
        b: u16,
        c: u32,
    }

    #[derive(serde::Serialize, serde::Deserialize, Debug)]
    struct TestStruct2 {
        x: u8,
        b: u16,
        c: u32,
    }

    let test_struct = TestStruct { a: 1, b: 2, c: 3 };
    let bincode_encoded = bincode::serialize(&test_struct).unwrap();
    let bincode_decoded: TestStruct2 = bincode::deserialize(&bincode_encoded).unwrap();
    eprintln!("Decoded: {:?}", bincode_decoded);
    //assert_eq!(test_struct.a, bincode_decoded.a);
}
