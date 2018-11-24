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

#define LEAF_GADGET(leaf_vk) protoboard<FieldT_B> pb;\
    pb_variable_array<FieldT_B> input_as_field_elements;\
    pb_variable_array<FieldT_B> input_as_bits;\
    \
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
	const size_t primary_input_size_in_bits = 298;\
	r1cs_ppzksnark_preprocessed_r1cs_ppzksnark_verification_key_variable<ppT_B> hardcoded_vk(pb, leaf_vk, "hardcoded_vk");\
	r1cs_ppzksnark_proof_variable<ppT_B> proof_1(pb, "proof_1");\
	pb_variable_array<FieldT_B> primary_input_1_bits_first_half;\
	pb_variable_array<FieldT_B> primary_input_1_bits_second_half;\
	primary_input_1_bits_first_half.allocate(pb, primary_input_size_in_bits, "primary_input_1_bits_first_half");\
	primary_input_1_bits_second_half.allocate(pb, primary_input_size_in_bits, "primary_input_1_bits_second_half");\
	pb_variable_array<FieldT_B> primary_input_1_bits;\
	primary_input_1_bits.insert(primary_input_1_bits.end(), primary_input_1_bits_first_half.begin(), primary_input_1_bits_first_half.end());\
    primary_input_1_bits.insert(primary_input_1_bits.end(), primary_input_1_bits_second_half.begin(), primary_input_1_bits_second_half.end());\
	r1cs_ppzksnark_proof_variable<ppT_B> proof_2(pb, "proof_2");\
	pb_variable_array<FieldT_B> primary_input_2_bits_first_half;\
	pb_variable_array<FieldT_B> primary_input_2_bits_second_half;\
	primary_input_2_bits_first_half.allocate(pb, primary_input_size_in_bits, "primary_input_2_bits_first_half");\
	primary_input_2_bits_second_half.allocate(pb, primary_input_size_in_bits, "primary_input_2_bits_second_half");\
	pb_variable_array<FieldT_B> primary_input_2_bits;\
	primary_input_2_bits.insert(primary_input_2_bits.end(), primary_input_2_bits_first_half.begin(), primary_input_2_bits_first_half.end());\
    primary_input_2_bits.insert(primary_input_2_bits.end(), primary_input_2_bits_second_half.begin(), primary_input_2_bits_second_half.end());\
	pb_variable<FieldT_B> result_1;\
	r1cs_ppzksnark_online_verifier_gadget<ppT_B> online_verifier_1(pb, hardcoded_vk, primary_input_1_bits, 596, proof_1, result_1, "online_verifier_1");\
	pb_variable<FieldT_B> result_2;\
	r1cs_ppzksnark_online_verifier_gadget<ppT_B> online_verifier_2(pb, hardcoded_vk, primary_input_2_bits, 596, proof_2, result_2, "online_verifier_2");\
	primary_input_1_bits_first_half.insert(primary_input_1_bits_first_half.end(), primary_input_1_bits.begin(), prev_root_digest.bits.end());\
	bit_vector_copy_gadget<FieldT_B> check_equal_1(pb, primary_input_1_bits_first_half, prev_root_digest.bits, pb_variable<FieldT_B>(1), FieldT_B::capacity(), FMT(annotation, " check_prev_hash_1"));\
	bit_vector_copy_gadget<FieldT_B> check_equal_2(pb, primary_input_1_bits_second_half, primary_input_2_bits_first_half, pb_variable<FieldT_B>(1), FieldT_B::capacity(), FMT(annotation, " check_next_hash_1"));\
	bit_vector_copy_gadget<FieldT_B> check_equal_3(pb, primary_input_2_bits_second_half, next_root_digest.bits, pb_variable<FieldT_B>(1), FieldT_B::capacity(), FMT(annotation, " check_next_hash_2"));\
	unpack_input.generate_r1cs_constraints(true);\
	proof_1.generate_r1cs_constraints();\
	proof_2.generate_r1cs_constraints();\
	online_verifier_1.generate_r1cs_constraints();\
	online_verifier_2.generate_r1cs_constraints();\
	check_equal_1.generate_r1cs_constraints(false, false);\
	check_equal_2.generate_r1cs_constraints(true, true);\
	check_equal_3.generate_r1cs_constraints(false, false);

template<typename ppT_A, typename ppT_B> void test_layer2_gen(const std::string &annotation) {
    typedef libff::Fr<ppT_A> FieldT_A;
	typedef CRH_with_bit_out_gadget<FieldT_A> HashT_A;
	typedef libff::Fr<ppT_B> FieldT_B;
    
    const size_t digest_len = HashT_A::get_digest_len();
    const size_t tree_depth = 16;
	
	// read the verifying key
    r1cs_ppzksnark_verification_key<ppT_A> leaf_vk;    
    ifstream fileIn("vk_leaf_unpacked");
    stringstream verificationKeyFromFile;
    if (fileIn) {
       verificationKeyFromFile << fileIn.rdbuf();
       fileIn.close();
    }
    verificationKeyFromFile >> leaf_vk;
    
    LEAF_GADGET(leaf_vk);
        
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

/*
template<typename ppT_A, typename FieldT_A, typename HashT_A> void test_leaf_example(const std::string &annotation) {
    auto tree_depth = 16;

    // read the proving key
    r1cs_ppzksnark_proving_key<ppT_A> pk;    
    ifstream fileIn("pk_leaf");
    stringstream provingKeyFromFile;
    if (fileIn) {
       provingKeyFromFile << fileIn.rdbuf();
       fileIn.close();
    }
    provingKeyFromFile >> pk;
    
    // generate the first test example -- we will use the same path because no tree is materalized
    const size_t digest_len = HashT_A::get_digest_len();
    std::vector<merkle_authentication_node> prev_path(tree_depth);

    // generate random leaf for before/after
    libff::bit_vector first_old_hash(digest_len);
    std::generate(first_old_hash.begin(), first_old_hash.end(), [&]() { return std::rand() % 2; });
    libff::bit_vector first_new_hash(digest_len);
    std::generate(first_new_hash.begin(), first_new_hash.end(), [&]() { return std::rand() % 2; });
    libff::bit_vector first_old_leaf = first_old_hash;
    libff::bit_vector first_new_leaf = first_new_hash;

    libff::bit_vector address_bits;
    size_t address = 0;
    for (long level = tree_depth-1; level >= 0; --level) {
        // sample a random address
        const bool computed_is_right = (std::rand() % 2);
        address |= (computed_is_right ? 1ul << (tree_depth-1-level) : 0);
        address_bits.push_back(computed_is_right);
        
        // sample random values for other nodes
        libff::bit_vector other(digest_len);
        std::generate(other.begin(), other.end(), [&]() { return std::rand() % 2; });

        // compute the upper layer's hash
        libff::bit_vector old_block = first_old_hash;
        old_block.insert(computed_is_right ? old_block.begin() : old_block.end(), other.begin(), other.end());
        libff::bit_vector new_block = first_new_hash;
        new_block.insert(computed_is_right ? new_block.begin() : new_block.end(), other.begin(), other.end());
        libff::bit_vector old_h = HashT_A::get_hash(old_block);
        libff::bit_vector new_h = HashT_A::get_hash(new_block);

        // save the neighborhood's hash
        prev_path[level] = other;

        first_old_hash = old_h;
        first_new_hash = new_h;
    }
    
    // save the root hash
    libff::bit_vector first_old_root = first_old_hash;
    libff::bit_vector first_new_root = first_new_hash;
    
    // declare the constraint system
    LEAF_GADGET
    
    const r1cs_constraint_system<FieldT_A> constraint_system = pb.get_constraint_system();
    cout << "Number of Leaf R1CS constraints: " << constraint_system.num_constraints() << endl;
    
    // place the input
    prev_root_digest.generate_r1cs_witness(first_old_root);
    next_root_digest.generate_r1cs_witness(first_new_root);
    
    unpack_input.generate_r1cs_witness_from_bits();
    
    address_bits_va.fill_with_bits(pb, address_bits);
    prev_leaf_digest.generate_r1cs_witness(first_old_leaf);
    prev_path_var.generate_r1cs_witness(address, prev_path);
    next_leaf_digest.generate_r1cs_witness(first_new_leaf);
    
    mls.generate_r1cs_witness();
        
    // =================================================================================================

    if(!pb.is_satisfied()){
        printf("The language is not accepted for proof 1.\n");
    }

    const size_t num_constraints = pb.num_constraints();
    cerr<<pb.primary_input().size()<<' '<<pb.auxiliary_input().size()<<endl;
    
    auto proof_1 = r1cs_ppzksnark_prover<ppT_A>(pk, pb.primary_input(), pb.auxiliary_input());
    
    stringstream proofStream;
    proofStream << proof_1;

    ofstream fileOut;
    fileOut.open("proof_1");
    fileOut << proofStream.rdbuf();
    fileOut.close();
    
    auto primary_input_1 = pb.primary_input();
    
    stringstream primaryinputStream;
    primaryinputStream << primary_input_1;

    fileOut.open("primary_input_1");
    fileOut << primaryinputStream.rdbuf();
    fileOut.close();
    
    // now let us do the second proof
    libff::bit_vector second_old_leaf = first_new_leaf;
    libff::bit_vector second_old_root = first_new_root;
        
    libff::bit_vector second_new_hash(digest_len);
    std::generate(second_new_hash.begin(), second_new_hash.end(), [&]() { return std::rand() % 2; });
    libff::bit_vector second_new_leaf = second_new_hash;
    
    long address_bit_read_back_counter = 0;
    for (long level = tree_depth-1; level >= 0; --level) {
        // come back to the same address
        const bool computed_is_right = address_bits[address_bit_read_back_counter++];
        
        // come back to the same other node
        libff::bit_vector other = prev_path[level];

        // compute the upper layer's hash
        libff::bit_vector new_block = second_new_hash;
        new_block.insert(computed_is_right ? new_block.begin() : new_block.end(), other.begin(), other.end());
        libff::bit_vector new_h = HashT_A::get_hash(new_block);

        second_new_hash = new_h;
    }
    
    // save the root hash
    libff::bit_vector second_new_root = second_new_hash;
    
    prev_root_digest.generate_r1cs_witness(second_old_root);
    next_root_digest.generate_r1cs_witness(second_new_root);
   	unpack_input.generate_r1cs_witness_from_bits();
    
    prev_leaf_digest.generate_r1cs_witness(second_old_leaf);
    prev_path_var.generate_r1cs_witness(address, prev_path);
    next_leaf_digest.generate_r1cs_witness(second_new_leaf);

    mls.generate_r1cs_witness();
    
    // generate the witnesses for the rest
    if(!pb.is_satisfied()){
        printf("The language is not accepted for proof 2.\n");
    }

    auto proof_2 = r1cs_ppzksnark_prover<ppT_A>(pk, pb.primary_input(), pb.auxiliary_input());
    
    proofStream << proof_2;

    fileOut.open("proof_2");
    fileOut << proofStream.rdbuf();
    fileOut.close();
    
    auto primary_input_2 = pb.primary_input();
    
    primaryinputStream << primary_input_2;

    fileOut.open("primary_input_2");
    fileOut << primaryinputStream.rdbuf();
    fileOut.close();
}

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
    //test_layer2_prove< libff::mnt4_pp, libff::mnt6_pp >("mnt4->6");
    //test_layer2_verifier<libff::mnt4_pp, libff::mnt6_pp >("mnt4->6");
}
