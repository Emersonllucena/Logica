module permissoes

--	Nome melhor para Entidade? (seria um arquivo OU diretorio)
abstract sig Entidade {
	paraTodos: one ParaTodos,
	usuarioExterno: one UsuarioExterno,
	usuarioLocal : one UsuarioLocal
}

sig Diretorio extends Entidade {
--	[Duvida] Diretorio pode ser vazio???
	conteudo: set Entidade
}

sig Arquivo extends Entidade {}

fun pai [ent:Entidade]: Diretorio {
	ent.~conteudo
}

pred root [dir:Diretorio] {
	no dir.~conteudo
}

pred ehCategoriaDe[cat:CategoriaUsuario, ent:Entidade] {
	(cat in ent.paraTodos) or (cat in ent.usuarioExterno) or (cat in ent.usuarioLocal)
}

fact estruturaDeArvore {
	-- nenhum diretorio é ancestral dele mesmo
	no dir: Diretorio | dir in dir.^conteudo

	-- todo arquivo possui um ancestral imediato
	all arq: Arquivo | one pai[arq]

	-- todo diretório possui um ou nenhum ancestral imediato
	all dir: Diretorio | lone pai[dir]

	-- apenas um diretorio nao possui ancestral imediato (root)
	one dir: Diretorio | root[dir]
}

abstract sig CategoriaUsuario {
	permissao: one Permissao
} {
	-- Toda categoria possui apenas um ancestral
	one ent: Entidade | ehCategoriaDe[this, ent]
}

sig ParaTodos, UsuarioExterno, UsuarioLocal extends CategoriaUsuario {}

abstract sig Permissao {}
	-- Funciona como um enum
one sig Leitura, LeituraEscrita, Dono extends Permissao {}

/*
Testa se as propriedades de árvore são respeitadas por todas as entidades.
*/
assert verificaArvore {
	-- A raíz deve ser um e apenas um diretório.
	one dir: Diretorio | root[dir] and no pai[dir]
	
	-- Nenhuma Entidade tem ela mesma como pai.
	all dir :Diretorio | not dir in dir.conteudo

	-- Para todas as entirades, ou ela tem um pai ou é a raiz.
	all ent: Entidade | #(ent.~conteudo) = 1 or root[ent]
}

check verificaArvore

pred show[]{}
run show for 10
