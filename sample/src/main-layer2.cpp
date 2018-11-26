/**
 *****************************************************************************
 * @author     This file is part of libsnark, developed by SCIPR Lab
 *             and contributors (see AUTHORS).
 * @copyright  MIT license (see LICENSE file)
 *****************************************************************************/

#include <libff/algebra/curves/mnt/mnt4/mnt4_pp.hpp>
#include <libff/algebra/curves/mnt/mnt6/mnt6_pp.hpp>
#include <libff/algebra/fields/field_utils.hpp>

#include <libsnark/gadgetlib1/gadgets/verifiers/r1cs_ppzksnark_verifier_gadget.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>
#include <libsnark/gadgetlib1/gadgets/merkle_tree/merkle_tree_check_update_gadget.hpp>
#include <libsnark/gadgetlib1/gadgets/basic_gadgets.hpp>

#include <iostream>
#include <fstream>
#include <sstream>

using namespace libsnark;
using namespace std;


void serialize_bit_vector_nonewline(std::ostream &out, const libff::bit_vector &v)
{
    out << v.size() << "\n";
    for (size_t i = 0; i < v.size(); ++i)
    {
        out << v[i] << "";
    }
}

#define LAYER2_GADGET(leaf_vk) protoboard<FieldT_B> pb;\
    pb_variable_array<FieldT_B> input_as_field_elements;\
    pb_variable_array<FieldT_B> input_as_bits;\
    const size_t input_size_in_bits = digest_len * 2;\
    {\
        const size_t input_size_in_field_elements = libff::div_ceil(input_size_in_bits, FieldT_B::capacity());\
        input_as_field_elements.allocate(pb, input_size_in_field_elements, "input_as_field_elements");\
        pb.set_input_sizes(input_size_in_field_elements);\
    }\
    digest_variable<FieldT_B> prev_root_digest(pb, digest_len, "prev_root_digest");\
    digest_variable<FieldT_B> next_root_digest(pb, digest_len, "next_root_digest");\
    input_as_bits.insert(input_as_bits.end(), prev_root_digest.bits.begin(), prev_root_digest.bits.end());\
    input_as_bits.insert(input_as_bits.end(), next_root_digest.bits.begin(), next_root_digest.bits.end());\
	assert(input_as_bits.size() == input_size_in_bits);\
    multipacking_gadget<FieldT_B> unpack_input(pb, input_as_bits, input_as_field_elements, FieldT_B::capacity(), FMT(annotation, " unpack_inputs"));\
	const size_t primary_input_size_in_bits = 3 * FieldT_A::size_in_bits();\
	r1cs_ppzksnark_preprocessed_r1cs_ppzksnark_verification_key_variable<ppT_B> hardcoded_vk(pb, leaf_vk, "hardcoded_vk");\
	r1cs_ppzksnark_proof_variable<ppT_B> proof_1(pb, "proof_1");\
	pb_variable_array<FieldT_B> primary_input_1_bits;\
	primary_input_1_bits.allocate(pb, primary_input_size_in_bits, "primary_input_1_bits");\
	r1cs_ppzksnark_proof_variable<ppT_B> proof_2(pb, "proof_2");\
	pb_variable_array<FieldT_B> primary_input_2_bits;\
	primary_input_2_bits.allocate(pb, primary_input_size_in_bits, "primary_input_2_bits");\
	pb_variable<FieldT_B> result_1;\
    result_1.allocate(pb, "result");\
	pb_variable<FieldT_B> result_2;\
    result_2.allocate(pb, "result");\
	r1cs_ppzksnark_online_verifier_gadget<ppT_B> online_verifier_1(pb, hardcoded_vk, primary_input_1_bits, FieldT_A::size_in_bits(), proof_1, result_1, "online_verifier_1");\
	r1cs_ppzksnark_online_verifier_gadget<ppT_B> online_verifier_2(pb, hardcoded_vk, primary_input_2_bits, FieldT_A::size_in_bits(), proof_2, result_2, "online_verifier_2");\
	pb_variable_array<FieldT_B> primary_input_1_bits_first_half;\
	primary_input_1_bits_first_half.insert(primary_input_1_bits_first_half.end(), primary_input_1_bits.begin() + 1 - 1, primary_input_1_bits_begin() + 297 - 1);\
	primary_input_1_bits_first_half.insert(primary_input_1_bits_first_half.end(), primary_input_1_bits.begin() + 299 - 1, primary_input_1_bits_begin() + 299 - 1);\
	pb_variable_array<FieldT_B> primary_input_1_bits_second_half;\
	primary_input_1_bits_second_half.insert(primary_input_1_bits_second_half.end(), primary_input_1_bits.begin() + 300 - 1, primary_input_1_bits_begin() + 593 - 1);\
	primary_input_1_bits_second_half.insert(primary_input_1_bits_second_half.end(), primary_input_1_bits.begin() + 595 - 1, primary_input_1_bits_begin() + 596 - 1);\
	bit_vector_copy_gadget<FieldT_B> check_equal_1(pb, prev_root_digest.bits, primary_input_1_bits_first_half.bits, pb_variable<FieldT_B>(1), FieldT_B::capacity(), FMT(annotation, " check_prev_hash_1"));\
	unpack_input.generate_r1cs_constraints(true);\
	proof_1.generate_r1cs_constraints();\
	proof_2.generate_r1cs_constraints();\
	online_verifier_1.generate_r1cs_constraints();\
	online_verifier_2.generate_r1cs_constraints();\
	check_equal_1.generate_r1cs_constraints(false, false);

	//bit_vector_copy_gadget<FieldT_B> check_equal_1(pb, primary_input_1_bits_first_half, prev_root_digest.bits, pb_variable<FieldT_B>(1), FieldT_B::capacity(), FMT(annotation, " check_prev_hash_1"));\
	//bit_vector_copy_gadget<FieldT_B> check_equal_2(pb, primary_input_1_bits_second_half, primary_input_2_bits_first_half, pb_variable<FieldT_B>(1), FieldT_B::capacity(), FMT(annotation, " check_next_hash_1"));\
	//bit_vector_copy_gadget<FieldT_B> check_equal_3(pb, primary_input_2_bits_second_half, next_root_digest.bits, pb_variable<FieldT_B>(1), FieldT_B::capacity(), FMT(annotation, " check_next_hash_2"));\
//	check_equal_1.generate_r1cs_constraints(false, false);\
//	check_equal_2.generate_r1cs_constraints(true, true);\
//	check_equal_3.generate_r1cs_constraints(false, false);

template<typename ppT_A, typename ppT_B> void test_layer2_gen(const std::string &annotation) {
    typedef libff::Fr<ppT_A> FieldT_A;
	typedef CRH_with_bit_out_gadget<FieldT_A> HashT_A;
	typedef libff::Fr<ppT_B> FieldT_B;
    
    const size_t digest_len = HashT_A::get_digest_len();
    const size_t tree_depth = 16;
	
	// read the verifying key
    r1cs_ppzksnark_verification_key<ppT_A> leaf_vk;    
    ifstream fileIn1("vk_packed_leaf");
    stringstream verificationKeyFromFile;
    if (fileIn1) {
       verificationKeyFromFile << fileIn1.rdbuf();
       fileIn1.close();
    }
    verificationKeyFromFile >> leaf_vk;
    
    LAYER2_GADGET(leaf_vk);
        
    const r1cs_constraint_system<FieldT_B> constraint_system = pb.get_constraint_system();
    cout << "Number of Leaf R1CS constraints: " << constraint_system.num_constraints() << endl;

    // generate a key pair
    const r1cs_ppzksnark_keypair<ppT_B> keypair = r1cs_ppzksnark_generator<ppT_B>(constraint_system);

    // save the verifying key
    stringstream vk_layer2;
    vk_layer2 << keypair.vk;
    
    ofstream fileOut;
    fileOut.open("vk_layer2");
    fileOut << vk_layer2.rdbuf();
    fileOut.close();
    
    // save the proving key
    stringstream pk_layer2;
    pk_layer2 << keypair.pk;
    
    fileOut.open("pk_layer2");
    fileOut << pk_layer2.rdbuf();
    fileOut.close();
}


template<typename ppT_A, typename ppT_B> void test_layer2_prove(const std::string &annotation) {
	typedef libff::Fr<ppT_A> FieldT_A;
	typedef CRH_with_bit_out_gadget<FieldT_A> HashT_A;
	typedef libff::Fr<ppT_B> FieldT_B;
	
    // read the proving key
    r1cs_ppzksnark_proving_key<ppT_B> pk;    
    ifstream fileIn("pk_layer2");
    stringstream provingKeyFromFile;
    if (fileIn) {
       provingKeyFromFile << fileIn.rdbuf();
       fileIn.close();
    }
    provingKeyFromFile >> pk;
	
	// read the proof 1 (packed)
    r1cs_ppzksnark_proof<ppT_A> proof_1_in;    
    ifstream fileIn2("proof_packed_1");
    stringstream proofFromFile;
    if (fileIn2) {
       proofFromFile << fileIn2.rdbuf();
       fileIn2.close();
    }
    proofFromFile >> proof_1_in;
	
    // read the input 1 (packed)
    r1cs_ppzksnark_primary_input<ppT_A> primary_input_1_in;
	ifstream fileIn3("primary_input_packed_1");
    if (fileIn3) {
        fileIn3 >> primary_input_1_in;
        fileIn3.close();
    }
	
    // read the proof 2 (packed)
    r1cs_ppzksnark_proof<ppT_A> proof_2_in;    
    ifstream fileIn4("proof_packed_2");
    if (fileIn4) {
       proofFromFile << fileIn4.rdbuf();
       fileIn4.close();
    }
    proofFromFile >> proof_2_in;
	
    // read the input 2 (packed)
    r1cs_ppzksnark_primary_input<ppT_A> primary_input_2_in;
    ifstream fileIn5("primary_input_packed_2");
    if (fileIn5) {
       fileIn5 >> primary_input_2_in;
       fileIn5.close();
    }
	
	const size_t primary_input_num_bits = 3 * FieldT_A::size_in_bits();
	
	libff::bit_vector primary_input_1_as_bits;
    for (const FieldT_A &el : primary_input_1_in)
    {
        libff::bit_vector v = libff::convert_field_element_to_bit_vector<FieldT_A>(el, FieldT_A::size_in_bits());
        primary_input_1_as_bits.insert(primary_input_1_as_bits.end(), v.begin(), v.end());
    }
	
	serialize_bit_vector_nonewline(cout, primary_input_1_as_bits);
	
	libff::bit_vector primary_input_2_as_bits;
    for (const FieldT_A &el : primary_input_2_in)
    {
        libff::bit_vector v = libff::convert_field_element_to_bit_vector<FieldT_A>(el, FieldT_A::size_in_bits());
        primary_input_2_as_bits.insert(primary_input_2_as_bits.end(), v.begin(), v.end());
    }
	
	// declare the constraint system    
    const size_t digest_len = HashT_A::get_digest_len();
	
	// read the verifying key
    r1cs_ppzksnark_verification_key<ppT_A> leaf_vk;    
    ifstream fileIn1("vk_packed_leaf");
    stringstream verificationKeyFromFile;
    if (fileIn1) {
       verificationKeyFromFile << fileIn1.rdbuf();
       fileIn1.close();
    }
    verificationKeyFromFile >> leaf_vk;
    
    LAYER2_GADGET(leaf_vk);
	
    const r1cs_constraint_system<FieldT_B> constraint_system = pb.get_constraint_system();
    cout << "Number of Leaf R1CS constraints: " << constraint_system.num_constraints() << endl;
	
	libff::bit_vector empty_hash_value(digest_len);
	
    //prev_root_digest.generate_r1cs_witness(empty_hash_value);
	//next_root_digest.generate_r1cs_witness(empty_hash_value);
	unpack_input.generate_r1cs_constraints(true);
	proof_1.generate_r1cs_witness(proof_1_in);
	primary_input_1_bits.fill_with_bits(pb, primary_input_1_as_bits);
	online_verifier_1.generate_r1cs_witness();
	pb.val(result_1) = FieldT_B::one();
	proof_2.generate_r1cs_witness(proof_2_in);
	primary_input_2_bits.fill_with_bits(pb, primary_input_2_as_bits);
	online_verifier_2.generate_r1cs_witness();
	pb.val(result_2) = FieldT_B::one();
	check_equal_1.generate_r1cs_witness();
	//check_equal_2.generate_r1cs_witness();
	//check_equal_3.generate_r1cs_witness();
        
    // =================================================================================================

    if(!pb.is_satisfied()){
        printf("The language is not accepted for proof.\n");
    }

    const size_t num_constraints = pb.num_constraints();
    cerr<<pb.primary_input().size()<<' '<<pb.auxiliary_input().size()<<endl;
    
    auto proof_layer2 = r1cs_ppzksnark_prover<ppT_B>(pk, pb.primary_input(), pb.auxiliary_input());
    
    stringstream proofStream;
    proofStream << proof_layer2;

    ofstream fileOut;
    fileOut.open("proof_layer2");
    fileOut << proofStream.rdbuf();
    fileOut.close();
    
    auto primary_input_layer2 = pb.primary_input();
    
    stringstream primaryinputStream;
    primaryinputStream << primary_input_layer2;

    fileOut.open("primary_input_layer2");
    fileOut << primaryinputStream.rdbuf();
    fileOut.close();
}

/*
template<typename ppT_A, typename FieldT_A, typename HashT_A> void test_leaf_verifier(const std::string &annotation) {
    auto tree_depth = 16;

    // read the verifying key
    r1cs_ppzksnark_verification_key<ppT_A> vk;    
    ifstream fileIn1("vk_leaf");
    stringstream verificationKeyFromFile;
    if (fileIn1) {
       verificationKeyFromFile << fileIn1.rdbuf();
       fileIn1.close();
    }
    verificationKeyFromFile >> vk;
    
    // read the proof 1
    r1cs_ppzksnark_proof<ppT_A> proof_1;    
    ifstream fileIn2("proof_1");
    stringstream proofFromFile;
    if (fileIn2) {
       proofFromFile << fileIn2.rdbuf();
       fileIn2.close();
    }
    proofFromFile >> proof_1;
    
    // read the input 1
    r1cs_ppzksnark_primary_input<ppT_A> primary_input_1;    
    ifstream fileIn3("primary_input_1");
    if (fileIn3) {
        fileIn3 >> primary_input_1;
        fileIn3.close();
    }
    
    // read the proof 2
    r1cs_ppzksnark_proof<ppT_A> proof_2;    
    ifstream fileIn4("proof_2");
    if (fileIn4) {
       proofFromFile << fileIn4.rdbuf();
       fileIn4.close();
    }
    proofFromFile >> proof_2;
    
    // read the input 2
    r1cs_ppzksnark_primary_input<ppT_A> primary_input_2;
    ifstream fileIn5("primary_input_2");
    if (fileIn5) {
       fileIn5 >> primary_input_2;
       fileIn5.close();
    }
	
	bool res_1 = r1cs_ppzksnark_verifier_strong_IC<ppT_A>(vk, primary_input_1, proof_1);
	bool res_2 = r1cs_ppzksnark_verifier_strong_IC<ppT_A>(vk, primary_input_2, proof_2);
	
	if(res_1 == false){
		printf("proof 1 is invalid.\n");
	}else{
		printf("proof 1 is valid.\n");
	}
	
	if(res_2 == false){
		printf("proof 2 is invalid.\n");
	}else{
		printf("proof 2 is valid.\n");
	}
}
*/


int main(void)
{
    libff::mnt4_pp::init_public_params();
	libff::mnt6_pp::init_public_params();

    test_layer2_gen< libff::mnt4_pp, libff::mnt6_pp >("mnt4->6");
    test_layer2_prove< libff::mnt4_pp, libff::mnt6_pp >("mnt4->6");
    //test_layer2_verifier<libff::mnt4_pp, libff::mnt6_pp >("mnt4->6");
}
