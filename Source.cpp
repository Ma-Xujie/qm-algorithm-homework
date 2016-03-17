#include <iostream>
#include <vector>
#include <algorithm>
#include <forward_list>
#include <vector>
#include <cstdio>
#include <queue>
#include <random>

using namespace std;

struct Minterm;
struct Implicant {  // �̺���
	inline Implicant(unsigned int d, unsigned int dc = 0U) :digs(d), dont_care(dc), isPrime(1) {}
	unsigned int digs;
	unsigned int dont_care;
	bool isPrime;

	void Print(int argc) {  // ������
		unsigned int mask = 1 << (argc - 1);
		char output_ch = 'A';
		char buffer[100] = { 0 };
		char *cur_char = buffer;
		while (mask) {
			if (mask & digs) {  // '1'
				*cur_char = output_ch++;
				++cur_char;
			} else if (mask & dont_care) {  // '-'
				// *cur_char = '-';
			} else {
				*cur_char = output_ch++;
				++cur_char;
				*cur_char = '\'';
				++cur_char;

			}
			mask >>= 1;
		}
		printf("%s ", buffer);
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

vector<vector<forward_list<Implicant> > > implicants;  // Implicants[�޹������][1 �ĸ���]
forward_list<Implicant> prime_implicants;  // �����̺���
vector<Minterm> minterms;  // ��С��
vector<vector<Minterm>::iterator> minterms_ptrs;  // ��С���ָ��
int min_cover_imps = 2147483647;  // INF
vector<vector<forward_list<Implicant>::iterator> > results;  // ���
queue<vector<forward_list<Implicant>::iterator> > result_queue;  // BFS ���ҽ��ʱ���õĶ���
queue<vector<vector<Minterm>::iterator > > minterm_queue;  // ͬ��

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

	auto prev_imp_ptr = prime_implicants.begin(); // ���ڴ��б�����ɷ�ʽ��ʵ���� PI.begin() һ���Ǳ�ԭ�̺���
	for (auto imp_ptr = prime_implicants.begin(); imp_ptr != prime_implicants.end(); ++imp_ptr) {
		if (!imp_ptr->isPrime) {
			imp_ptr = prev_imp_ptr;
			prime_implicants.erase_after(prev_imp_ptr);  // �ѵ�ǰ����ɾ��
		} else {
			prev_imp_ptr = imp_ptr;
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

	// ����С����ܹ��������ı����̺������������
	sort(minterms.begin(), minterms.end(),
		[](const Minterm &mt1, const Minterm &mt2) {return mt1.covered_imps.size() < mt2.covered_imps.size(); });

	for (auto ptr = minterms.begin(); ptr != minterms.end(); ++ptr) {
		minterms_ptrs.push_back(ptr);
	}

	// ��ʼ�� BFS �Ķ���
	vector<forward_list<Implicant>::iterator> empty_result;
	result_queue.push(empty_result);
	minterm_queue.push(minterms_ptrs);

	// �ù����������������С����
	while (!result_queue.empty()) {  // ��ֹ�����Ƕ���Ϊ��
		auto result = result_queue.front();  // �Ӷ����е���һ��
		auto minterms_ptr = minterm_queue.front();
		result_queue.pop();
		minterm_queue.pop();

		if (result.size() > min_cover_imps) {
			continue;
		}

		if (minterms_ptr.empty()) {  // ��������ĸ��ǿ�����ȫ����������С��
			min_cover_imps = result.size();  // ����С���ǵĹ�ģ����Ϊ�˸��ǵĹ�ģ
			results.push_back(result);   // �ڴ�����Ӵ˽��
			continue;
		} else if (result.size() == min_cover_imps) {  // ��ֹû��ϣ���ĸ������
			continue;
		}
		if (result_queue.size() > 2000000) {  // Ϊ�������к�ջ���޷�����������˴����������еĳ����������ơ�����������ս�������������ڴ˽��޵�ʱ���п����޷�������н�������߽��������С����
			// printf("WARNING!\n");
			continue;
		}
		for (auto next_imp : minterms_ptr.front()->covered_imps) {  // �� BST ���������м��������Ҫ������·��
			minterm_queue.emplace(minterms_ptr);
			result_queue.emplace(result);
			result_queue.back().push_back(next_imp);  // ��ǰ����·�������һ�����
			auto erase_begin = remove_if(minterm_queue.back().begin(), minterm_queue.back().end(),
				[next_imp](vector<Minterm>::iterator m) {return CanBeCovered(m->digs, *next_imp); });  // �����������������Ը��ǵ�������С��
			minterm_queue.back().erase(erase_begin, minterm_queue.back().end());
		}
	}
}

int main() {
	// QM(2, { 0, 1, 2, 3 }, {});
	// QM(3, { 0, 4, 5, 7 }, {});
	// QM(4, { 1, 3, 4, 5, 6, 10, 11, 13, 14, 15 }, {});
	vector<unsigned int> tmp;
	vector<unsigned int> dc;
	for (unsigned int i = 0; i != 1000; ++i) {
		if (rand() % 10 == 0) {
			tmp.push_back(i);
		} else if (rand() % 20 == 0) {
			dc.push_back(i);
		}
	}
	QM(10, tmp, dc);
	for (auto x : results) {
		for (auto t : x) {
			t->Print(10);
		}
		printf("\n");
	}
}