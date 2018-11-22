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

#define LEAF_GADGET_WITHPACKING protoboard<FieldT_A> pb;\
    pb_variable_array<FieldT_A> input_as_field_elements;\
    pb_variable_array<FieldT_A> input_as_bits;\
    \
    const size_t input_size_in_bits = digest_len * 2;\
    {\
        const size_t input_size_in_field_elements = libff::div_ceil(input_size_in_bits, FieldT_A::capacity());\
        input_as_field_elements.allocate(pb, input_size_in_field_elements, "input_as_field_elements");\
        pb.set_input_sizes(input_size_in_field_elements);\
    }\
    \
    digest_variable<FieldT_A> prev_root_digest(pb, digest_len, "prev_root_digest");\
    digest_variable<FieldT_A> next_root_digest(pb, digest_len, "next_root_digest");\
    input_as_bits.insert(input_as_bits.end(), prev_root_digest.bits.begin(), prev_root_digest.bits.end());\
    input_as_bits.insert(input_as_bits.end(), next_root_digest.bits.begin(), next_root_digest.bits.end());\
    assert(input_as_bits.size() == input_size_in_bits);\
    multipacking_gadget<FieldT_A> unpack_input(pb, input_as_bits, input_as_field_elements, FieldT_A::capacity(), FMT(annotation, " unpack_inputs"));\
    pb_variable_array<FieldT_A> address_bits_va;\
    address_bits_va.allocate(pb, tree_depth, "address_bits");\
    digest_variable<FieldT_A> prev_leaf_digest(pb, digest_len, "prev_leaf_digest");\
    digest_variable<FieldT_A> next_leaf_digest(pb, digest_len, "next_leaf_digest");\
    merkle_authentication_path_variable<FieldT_A, HashT_A> prev_path_var(pb, tree_depth, "prev_path_var");\
    merkle_authentication_path_variable<FieldT_A, HashT_A> next_path_var(pb, tree_depth, "next_path_var");\
    merkle_tree_check_update_gadget<FieldT_A, HashT_A> mls(pb, tree_depth, address_bits_va,\
                                                         prev_leaf_digest, prev_root_digest, prev_path_var,\
                                                         next_leaf_digest, next_root_digest, next_path_var, pb_variable<FieldT_A>(0), "mls");\
    unpack_input.generate_r1cs_constraints(true);\
    prev_path_var.generate_r1cs_constraints();\
    mls.generate_r1cs_constraints();

#define LEAF_GADGET protoboard<FieldT_A> pb;\
    pb.set_input_sizes(digest_len * 2);\
    digest_variable<FieldT_A> prev_root_digest(pb, digest_len, "prev_root_digest");\
    digest_variable<FieldT_A> next_root_digest(pb, digest_len, "next_root_digest");\
    pb_variable_array<FieldT_A> address_bits_va;\
    address_bits_va.allocate(pb, tree_depth, "address_bits");\
    digest_variable<FieldT_A> prev_leaf_digest(pb, digest_len, "prev_leaf_digest");\
    digest_variable<FieldT_A> next_leaf_digest(pb, digest_len, "next_leaf_digest");\
    merkle_authentication_path_variable<FieldT_A, HashT_A> prev_path_var(pb, tree_depth, "prev_path_var");\
    merkle_authentication_path_variable<FieldT_A, HashT_A> next_path_var(pb, tree_depth, "next_path_var");\
    merkle_tree_check_update_gadget<FieldT_A, HashT_A> mls(pb, tree_depth, address_bits_va,\
                                                         prev_leaf_digest, prev_root_digest, prev_path_var,\
                                                         next_leaf_digest, next_root_digest, next_path_var, pb_variable<FieldT_A>(0), "mls");\
    prev_path_var.generate_r1cs_constraints();\
    mls.generate_r1cs_constraints();

/*template<typename ppT_A, typename ppT_B> r1cs_example<libff::Fr<ppT_B> > test_verifier_B(const r1cs_example<libff::Fr<ppT_A> > &example, const std::string &annotation_A, const std::string &annotation_B, size_t &vk_size_in_Fields)
{
        typedef libff::Fr<ppT_A> FieldT_A;
        typedef libff::Fr<ppT_B> FieldT_B;

        assert(example.constraint_system.is_satisfied(example.primary_input, example.auxiliary_input));
       
        const r1cs_ppzksnark_proof<ppT_A> pi = r1cs_ppzksnark_prover<ppT_A>(keypair.pk, example.primary_input, example.auxiliary_input);

        const size_t elt_size = FieldT_A::size_in_bits();
        const size_t primary_input_size_in_bits = elt_size * example.constraint_system.primary_input_size;
        const size_t vk_size_in_bits = r1cs_ppzksnark_verification_key_variable<ppT_B>::size_in_bits(example.constraint_system.primary_input_size);
}*/

template<typename ppT_A, typename HashT_A> void test_leaf_gen(const std::string &annotation) {
    typedef libff::Fr<ppT_A> FieldT_A;
    
    const size_t digest_len = HashT_A::get_digest_len();
    const size_t tree_depth = 16;
    
    LEAF_GADGET
        
    const r1cs_constraint_system<FieldT_A> constraint_system = pb.get_constraint_system();
    cout << "Number of Leaf R1CS constraints: " << constraint_system.num_constraints() << endl;

    // generate a key pair
    const r1cs_ppzksnark_keypair<ppT_A> keypair = r1cs_ppzksnark_generator<ppT_A>(constraint_system);

    // save the verifying key
    stringstream vk_leaf;
    vk_leaf << keypair.vk;
    
    ofstream fileOut;
    fileOut.open("vk_leaf");
    fileOut << vk_leaf.rdbuf();
    fileOut.close();
    
    // save the proving key
    stringstream pk_leaf;
    pk_leaf << keypair.pk;
    
    fileOut.open("pk_leaf");
    fileOut << pk_leaf.rdbuf();
    fileOut.close();
}

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
    // add an error
    first_new_root = first_new_leaf;
    
    serialize_bit_vector_nonewline(cout, first_old_root);
    serialize_bit_vector_nonewline(cout, first_new_root);
    serialize_bit_vector_nonewline(cout, first_old_leaf);
    serialize_bit_vector_nonewline(cout, first_new_leaf);
    
    // declare the constraint system
    LEAF_GADGET
    
    const r1cs_constraint_system<FieldT_A> constraint_system = pb.get_constraint_system();
    cout << "Number of Leaf R1CS constraints: " << constraint_system.num_constraints() << endl;
    
    // place the input
    prev_root_digest.generate_r1cs_witness(first_old_root);
    next_root_digest.generate_r1cs_witness(first_new_root);
    
    //unpack_input.generate_r1cs_witness_from_bits();
    
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
   // unpack_input.generate_r1cs_witness_from_bits();
    
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
       primary_input_1 << fileIn3;
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
       primary_input_2<< fileIn5;
       fileIn5.close();
    }
}

    /*

 
    r1cs_example<FieldT_B> verifier_1 = test_verifier_B< ppT_A, ppT_B >(new_example, annotation_A, annotation_B, vk_size_in_Fields);

        // try recursive proofs
        cerr<<"start second proof"<<endl;
        
        r1cs_example<FieldT_B> verifier_2 = test_verifier_B< ppT_A, ppT_B >(another_example, annotation_A, annotation_B, vk_size_in_Fields);
        verifier_2.constraint_system = verifier_1.constraint_system;
        //protoboard<FieldT_B> pb_2(pb_1.get_constraint_system, another_example.primary_input, another_example.auxiliary_input);


        //r1cs_example<FieldT_B> cs(pb_1.get_constraint_system(), pb_2.primary_input(), pb_2.auxiliary_input());
        //cerr<<cs.constraint_system.is_satisfied(cs.primary_input, cs.auxiliary_input)<<endl;
        //exit(0);

        // merge proof
        r1cs_example<FieldT_B> final_example = merge_verifier< ppT_A, ppT_B, FieldT_A, FieldT_B>(verifier_1, verifier_2);

        cerr<<"test final proof"<<endl;
        assert(final_example.constraint_system.is_satisfied(final_example.primary_input, final_example.auxiliary_input));
        cerr<<final_example.constraint_system.is_satisfied(final_example.primary_input, final_example.auxiliary_input)<<endl;

        size_t primary_input_size_1 = verifier_1.primary_input.size();
        size_t digest_len = HashT_B::get_digest_len();
        cerr<<HashT_A::get_digest_len() << ' '<<HashT_B::get_digest_len()<<endl;
        assert(HashT_A::get_digest_len() ==  HashT_B::get_digest_len());
        merge_inputs<FieldT_B>(final_example, vk_size_in_Fields + 1 + digest_len*2, vk_size_in_Fields + 1 + digest_len*4, primary_input_size_1 + vk_size_in_Fields + 1, primary_input_size_1 + vk_size_in_Fields + 1 + digest_len*2);
        merge_inputs<FieldT_B>(final_example, 0, vk_size_in_Fields-1, primary_input_size_1, primary_input_size_1 + vk_size_in_Fields - 1);

        cerr<<final_example.constraint_system.is_satisfied(final_example.primary_input, final_example.auxiliary_input)<<endl;
    */

int main(void)
{
    libff::start_profiling();
    libff::mnt4_pp::init_public_params();
    
    typedef libff::Fr<libff::mnt4_pp> FieldT_A;

    //test_leaf_gen< libff::mnt4_pp, CRH_with_bit_out_gadget<libff::Fr<libff::mnt4_pp>> >("mnt4");
    test_leaf_example<libff::mnt4_pp, FieldT_A, CRH_with_bit_out_gadget<FieldT_A> >("mnt4");
    test_leaf_verifier<libff::mnt4_pp, FieldT_A, CRH_with_bit_out_gadget<FieldT_A> >("mnt4");
}
