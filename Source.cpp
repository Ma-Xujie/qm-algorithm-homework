#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <forward_list>
#include <vector>
#include <cstdio>
#include <queue>
#include <random>
#include <ctime>

using namespace std;

struct Implicant {  // �̺���
	inline Implicant(unsigned int d, unsigned int dc = 0U) :digs(d), dont_care(dc), isPrime(1) {}
	unsigned int digs;
	unsigned int dont_care;
	bool isPrime;

	void PPrint(int argc) {  // Pretty Print
		unsigned int mask = 1 << (argc - 1);
		char buffer[100] = { 0 };
		char *cur_char = buffer;
		char cur_var = 'A';
		while (mask) {
			if (mask & digs) {
				sprintf(cur_char, "%c", cur_var);
				++cur_char;
				++cur_var;
			} else if (mask & dont_care) {
				++cur_var;
			} else {
				sprintf(cur_char, "%c'", cur_var);
				cur_char += 2;
				++cur_var;
			}
			mask >>= 1;
		}
		if (strlen(buffer) == 0) {
			sprintf(buffer, "(null)");
		}
		printf("%s", buffer);
	}
};

struct Minterm {  // ��С��
	inline Minterm(unsigned int d) :digs(d), covered(false) {}
	unsigned int digs;
	bool covered;
	vector<forward_list<Implicant>::iterator> covered_imps;  // �����С����б��еı����̺����
};

inline int CountOnes(unsigned int x) {  // ��һ����С���� 1 �ĸ���
	unsigned int mask = 1;
	int counter = 0;
	while (mask) {
		counter += ((x & mask) > 0);
		mask <<= 1;
	}
	return counter;
}

inline bool CanBeCovered(unsigned m, const Implicant &imp) {  // �ж�һ����С���Ƿ���Ա�һ���̺����
	return (m & (~imp.dont_care)) == imp.digs;
}

vector<vector<forward_list<Implicant> > > implicants;  // implicants['-'����][1 �ĸ���]
forward_list<Implicant> prime_implicants;  // �����̺���
vector<Minterm> minterms;  // ��С��
vector<vector<Minterm>::iterator> minterms_ptrs;  // ��С���ָ��
int cur_min_result_size = 2147483647;  // ��ǰ�Ѿ��ҵ�����С���ǵĹ�ģ��������������� DFS ��������֦
vector<vector<forward_list<Implicant>::iterator> > results;  // ���
vector<vector<forward_list<Implicant>::iterator> > result_stack;  // DFS ���ҽ��ʱ���õ�ջ
vector<vector<vector<Minterm>::iterator > > minterm_stack;  // ͬ��

void QM(int argc, vector<unsigned int> ms, vector<unsigned int> dcs) {  // ���������Ĳ������� & ��С�� & �޹���
	implicants.resize(argc + 1);
	implicants[0].resize(argc + 1);
	implicants[1].resize(argc);

	// ��ʼ��
	for (auto m : ms) {
		implicants[0][CountOnes(m)].emplace_front(m);
		minterms.emplace_back(m);
	}
	for (auto dc : dcs) {
		implicants[0][CountOnes(dc)].emplace_front(dc);
	}

	// �ϲ��̺���
	int cur_ones = 0, cur_dcs = 0;
	while (cur_dcs < argc) {
		implicants[cur_dcs + 1].resize(argc - cur_dcs);
		while (cur_ones < argc - cur_dcs) {
			auto &cur_list = implicants[cur_dcs][cur_ones];
			auto &more_one_list = implicants[cur_dcs][cur_ones + 1];  // cur_ones + 1 ����� argc - cur_dcs, ��ʾ���� dc ������ȫ���� 1
			auto &more_dc_list = implicants[cur_dcs + 1][cur_ones];

			for (auto &m1 : cur_list) {
				for (auto &m2 : more_one_list) {
					unsigned int diff = m2.digs ^ m1.digs;
					if (m1.dont_care == m2.dont_care && CountOnes(diff) == 1) { // ����û�����⣬�ɺϲ�������� m2 �����ҽ���һλ�� m1 �� 1
						bool flag = true;
						for (auto imp : more_dc_list) {  // ȥ��
							if (imp.digs == m1.digs && imp.dont_care == (m1.dont_care | diff)) {
								flag = false;
								break;
							}
						}
						if (flag) {
							more_dc_list.emplace_front(m1.digs, (m1.dont_care | diff));
							m1.isPrime = false;
							m2.isPrime = false;
						}
					}
				}
			}
			++cur_ones;
		}
		++cur_dcs;
		cur_ones = 0;
	}

	// ɸѡ�����б�ԭ�̺���
	for (auto &imp_list_list : implicants) {
		for (auto &imp_list : imp_list_list) {
			prime_implicants.splice_after(prime_implicants.before_begin(), imp_list);  // ���Ȱ����д�ǰ�ҵ����̺���ӳ�һ������
		}
	}
	int prime_imp_number = 0;
	auto prev_imp_ptr = prime_implicants.begin(); // ���ڴ��б�����ɷ�ʽ��ʵ���� PI.begin() һ���Ǳ�ԭ�̺���
	for (auto imp_ptr = prime_implicants.begin(); imp_ptr != prime_implicants.end(); ++imp_ptr) {
		if (!imp_ptr->isPrime) {  // ���ĳһ��Ǳ�ԭ�̺���
			imp_ptr = prev_imp_ptr;
			prime_implicants.erase_after(prev_imp_ptr);  // ����һ��ɾ��
		} else {
			prev_imp_ptr = imp_ptr;
			++prime_imp_number;
		}
	}

	// ��ÿ����С�����ܸ��Ǹ���С������б����̺������Ӧ��ϵ
	for (auto &minterm : minterms) {
		for (auto imp = prime_implicants.begin(); imp != prime_implicants.end(); ++imp) {
			if (CanBeCovered(minterm.digs, *imp)) {
				minterm.covered_imps.push_back(imp);
			}
		}
	}

	// ����С����ܹ��������ı����̺�����������򣬾���������ʱ�ԭ�̺�����ȱ�ѡ��
	sort(minterms.begin(), minterms.end(),
		[](const Minterm &mt1, const Minterm &mt2) {return mt1.covered_imps.size() < mt2.covered_imps.size(); });

	// Ϊ�����ڽ������������ж�θ�����С���������ֻʹ����С���ָ��
	for (auto ptr = minterms.begin(); ptr != minterms.end(); ++ptr) {
		minterms_ptrs.push_back(ptr);
	}

	// DFS
	printf("Estimating result size");
	int try_times = 20000 * (min(prime_imp_number, 200));
	srand(clock());
	for (int i = 0; i != try_times; ++i) {  // ��������������ɴγ��ԣ�������С���ǵĹ�ģ��Ϊ DFS ��֦���ӿ������ٶ�
		int cnt = 0;
		auto mt_ptrs = minterms_ptrs;
		while (!mt_ptrs.empty() && mt_ptrs.size() <= cur_min_result_size) {
			auto next_imp = mt_ptrs.front()->covered_imps[rand() % mt_ptrs.front()->covered_imps.size()];
			auto erase_begin = remove_if(mt_ptrs.begin(), mt_ptrs.end(),
				[next_imp](vector<Minterm>::iterator m) {return CanBeCovered(m->digs, *next_imp); });  // �����������������Ը��ǵ�������С��
			mt_ptrs.erase(erase_begin, mt_ptrs.end());
			++cnt;
		}
		if (mt_ptrs.empty() && cnt < cur_min_result_size) {
			cur_min_result_size = cnt;
		}
		if (i % 1000000 == 0) { printf("."); }  // ����һ���Ӿ�Ч��..
	}

	// ��ʼ�� DFS �Ķ��У�������������С���б�Ϳ�·��
	vector<forward_list<Implicant>::iterator> empty_result;
	result_stack.push_back(empty_result);
	minterm_stack.push_back(minterms_ptrs);

	// �������������������С����
	printf("\nStart Search");
	unsigned int i = 0;
	while (!result_stack.empty()) {  // ��ֹ������ջΪ�գ���֤�����ҵ�������С����
		if (++i % 1000000 == 0) { printf("."); }  // ����һ���Ӿ�Ч��..

		auto result = result_stack.back();  // ��ջ�е���һ����Ϊ��ǰҪ������·��
		auto minterms_ptr = minterm_stack.back();
		result_stack.pop_back();
		minterm_stack.pop_back();

		if (result.size() > cur_min_result_size) {  // �����·���ĳ����Ѿ�������֪����С���ǹ�ģ���������һ·��
			continue;
		}

		if (minterms_ptr.empty()) {  // ���������·��������ȫ����������С��
			if (result.size() < cur_min_result_size) {  // �������ģС����֪��С���ǹ�ģ
				results.clear();  // ������ǰ�Ѿ��ҵ��Ľ��
				cur_min_result_size = result.size();  // ����С���ǵĹ�ģ����Ϊ�˸��ǵĹ�ģ
			}
			results.push_back(result);   // �ڴ�����Ӵ˽��
			continue;
		} else if (result.size() == cur_min_result_size) {  // ��ֹû��ϣ���ĸ�����ջ
			continue;
		}

		for (auto next_imp : minterms_ptr.front()->covered_imps) {  // �� DFS ����ջ�м��������Ҫ������·��
			minterm_stack.emplace_back(minterms_ptr);
			result_stack.emplace_back(result);
			result_stack.back().push_back(next_imp);  // ��ǰ����·�������һ�����
			auto erase_begin = remove_if(minterm_stack.back().begin(), minterm_stack.back().end(),
				[next_imp](vector<Minterm>::iterator m) {return CanBeCovered(m->digs, *next_imp); });  // �������������������Ը��ǵ�������С��
			minterm_stack.back().erase(erase_begin, minterm_stack.back().end());
		}
	}
	printf("\n");
}

void PrintResult(int argc, const vector<forward_list<Implicant>::iterator> &result) {
	for (int i = 0; i != result.size(); ++i) {
		result[i]->PPrint(argc);
		if (i != result.size() - 1) {
			printf("+");
		}
	}
	printf("\n");
}

int main() {
	int argc;
	int minterm_num, dc_num;
	vector<unsigned int> minterms, dcs;

	// ��ȡ���룬δ�������ʽ���
	cout << "Boolean Expression Simplifier by ma-xujie" << endl;
	cout << "Please Input Number Of Boolean Variables:" << endl;
	cin >> argc;
	cout << "Please Input Number Of Minterms:" << endl;
	cin >> minterm_num;
	cout << "Please Input Minterms:" << endl;
	for (int i = 0; i != minterm_num; ++i) {
		unsigned int tmp;
		cin >> tmp;
		minterms.push_back(tmp);
	}
	cout << "Please Input Number Of Don't Care Terms:" << endl;
	cin >> dc_num;
	if (dc_num > 0) {
		cout << "Please Input Don't Care Terms:" << endl;
		for (int i = 0; i != dc_num; ++i) {
			unsigned int tmp;
			cin >> tmp;
			dcs.push_back(tmp);
		}
	}

	// ����
	QM(argc, minterms, dcs);

	// ��ӡ���
	cout << "Done!" << endl;
	cout << results.size() << " Result(s)" << endl;
	if (results.size() == 1) {
		PrintResult(argc, results.front());
	} else {
		string ctrl;
		cin.clear();
		cin.ignore(10000000, '\n');
		cout << "Print All Results?(Y/n)\n";
		ctrl = cin.get();
		if (ctrl == "n" || ctrl == "N") {
			PrintResult(argc, results.front());
		} else {
			for (auto &result : results) {
				PrintResult(argc, result);
			}
		}
	}
}
